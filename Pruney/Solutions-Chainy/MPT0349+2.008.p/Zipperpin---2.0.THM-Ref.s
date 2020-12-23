%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mrpfqpaKwJ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  60 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  261 ( 307 expanded)
%              Number of equality atoms :   38 (  45 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t22_subset_1,conjecture,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k2_subset_1 @ A )
        = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_subset_1])).

thf('0',plain,(
    ( k2_subset_1 @ sk_A )
 != ( k3_subset_1 @ sk_A @ ( k1_subset_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( k1_subset_1 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('2',plain,(
    ( k2_subset_1 @ sk_A )
 != ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    sk_A
 != ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X46 ) @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('6',plain,(
    ! [X42: $i] :
      ( ( k1_subset_1 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('7',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k3_subset_1 @ X44 @ X45 )
        = ( k4_xboole_0 @ X44 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A
 != ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['10','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mrpfqpaKwJ
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 70 iterations in 0.031s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.50  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(t22_subset_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t22_subset_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ (k1_subset_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('1', plain, (![X42 : $i]: ((k1_subset_1 @ X42) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.50  thf('3', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.50  thf('4', plain, (((sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(dt_k1_subset_1, axiom,
% 0.21/0.50    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X46 : $i]: (m1_subset_1 @ (k1_subset_1 @ X46) @ (k1_zfmisc_1 @ X46))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.21/0.50  thf('6', plain, (![X42 : $i]: ((k1_subset_1 @ X42) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X46 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(d5_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X44 : $i, X45 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X44 @ X45) = (k4_xboole_0 @ X44 @ X45))
% 0.21/0.50          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, (((sk_A) != (k4_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.50  thf(t5_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('11', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.50  thf(t95_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k3_xboole_0 @ A @ B ) =
% 0.21/0.50       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ X9 @ X10)
% 0.21/0.50           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.21/0.50           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf(t1_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('14', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.50  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.50  thf(t100_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.21/0.50           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf(t92_xboole_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('23', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.50  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['21', '26'])).
% 0.21/0.50  thf('28', plain, (((sk_A) != (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '27'])).
% 0.21/0.50  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
