%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OCZyx0sdAv

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 (  89 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  402 ( 540 expanded)
%              Number of equality atoms :   55 (  72 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X41: $i] :
      ( ( k1_subset_1 @ X41 )
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
    ! [X42: $i] :
      ( ( k2_subset_1 @ X42 )
      = X42 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    sk_A
 != ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X41: $i] :
      ( ( k1_subset_1 @ X41 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X45 ) @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X43 @ X44 )
        = ( k4_xboole_0 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
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

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('20',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('37',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['10','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OCZyx0sdAv
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 198 iterations in 0.080s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(t22_subset_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t22_subset_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ (k1_subset_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('1', plain, (![X41 : $i]: ((k1_subset_1 @ X41) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.53  thf('3', plain, (![X42 : $i]: ((k2_subset_1 @ X42) = (X42))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf('4', plain, (((sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain, (![X41 : $i]: ((k1_subset_1 @ X41) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.53  thf(dt_k1_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X45 : $i]: (m1_subset_1 @ (k1_subset_1 @ X45) @ (k1_zfmisc_1 @ X45))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X43 : $i, X44 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))
% 0.20/0.53          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain, (((sk_A) != (k4_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '9'])).
% 0.20/0.53  thf(t95_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.53       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X10 @ X11)
% 0.20/0.53           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.20/0.53              (k2_xboole_0 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.20/0.53  thf(l51_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X39 : $i, X40 : $i]:
% 0.20/0.53         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.20/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.53  thf(t91_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.20/0.53           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X10 @ X11)
% 0.20/0.53           = (k5_xboole_0 @ X10 @ 
% 0.20/0.53              (k5_xboole_0 @ X11 @ (k3_tarski @ (k2_tarski @ X10 @ X11)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.53  thf(t92_xboole_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('15', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.20/0.53           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ k1_xboole_0 @ (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 0.20/0.53           = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['14', '17'])).
% 0.20/0.53  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.53  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X39 : $i, X40 : $i]:
% 0.20/0.53         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.20/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.53  thf('21', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.53  thf('22', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.53  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['18', '21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X10 @ X11)
% 0.20/0.53           = (k5_xboole_0 @ X10 @ 
% 0.20/0.53              (k5_xboole_0 @ X11 @ (k3_tarski @ (k2_tarski @ X10 @ X11)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.53           = (k5_xboole_0 @ X0 @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf(t1_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('26', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X39 : $i, X40 : $i]:
% 0.20/0.53         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.20/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X4 : $i]: ((k3_tarski @ (k2_tarski @ X4 @ k1_xboole_0)) = (X4))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '28'])).
% 0.20/0.53  thf('30', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.53  thf(t100_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.53           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.53           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.53           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('37', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.53  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf(t5_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('39', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '40'])).
% 0.20/0.53  thf('42', plain, (((sk_A) != (sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '41'])).
% 0.20/0.53  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
