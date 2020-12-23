%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Efin8BQmAn

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:44 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 102 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  424 ( 654 expanded)
%              Number of equality atoms :   58 (  86 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X40: $i] :
      ( ( k1_subset_1 @ X40 )
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
    ! [X41: $i] :
      ( ( k2_subset_1 @ X41 )
      = X41 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    sk_A
 != ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k3_subset_1 @ X42 @ X43 )
        = ( k4_xboole_0 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    sk_A
 != ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('18',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('25',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('35',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','43'])).

thf('45',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['8','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Efin8BQmAn
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 217 iterations in 0.125s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.61  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.39/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.61  thf(t22_subset_1, conjecture,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]:
% 0.39/0.61        ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t22_subset_1])).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ (k1_subset_1 @ sk_A)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.61  thf('1', plain, (![X40 : $i]: ((k1_subset_1 @ X40) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.61  thf('3', plain, (![X41 : $i]: ((k2_subset_1 @ X41) = (X41))),
% 0.39/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.61  thf('4', plain, (((sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf(t4_subset_1, axiom,
% 0.39/0.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X44 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X44))),
% 0.39/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.61  thf(d5_subset_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X42 : $i, X43 : $i]:
% 0.39/0.61         (((k3_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))
% 0.39/0.61          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.61  thf('8', plain, (((sk_A) != (k4_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['4', '7'])).
% 0.39/0.61  thf(t95_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k3_xboole_0 @ A @ B ) =
% 0.39/0.61       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ X9 @ X10)
% 0.39/0.61           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.39/0.61  thf(l51_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X38 : $i, X39 : $i]:
% 0.39/0.61         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.39/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.61  thf(t91_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.61       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.39/0.61           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ X9 @ X10)
% 0.39/0.61           = (k5_xboole_0 @ X9 @ 
% 0.39/0.61              (k5_xboole_0 @ X10 @ (k3_tarski @ (k2_tarski @ X9 @ X10)))))),
% 0.39/0.61      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.39/0.61  thf(t92_xboole_1, axiom,
% 0.39/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.61  thf('13', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.39/0.61           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.61           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((k5_xboole_0 @ k1_xboole_0 @ (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 0.39/0.61           = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['12', '15'])).
% 0.39/0.61  thf(idempotence_k2_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.61  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.61      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X38 : $i, X39 : $i]:
% 0.39/0.61         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.39/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.61  thf('19', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.61  thf('20', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.61  thf('21', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ X9 @ X10)
% 0.39/0.61           = (k5_xboole_0 @ X9 @ 
% 0.39/0.61              (k5_xboole_0 @ X10 @ (k3_tarski @ (k2_tarski @ X9 @ X10)))))),
% 0.39/0.61      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.39/0.61           = (k5_xboole_0 @ X0 @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 0.39/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.39/0.61  thf(t1_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.61  thf('24', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X38 : $i, X39 : $i]:
% 0.39/0.61         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.39/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (![X4 : $i]: ((k3_tarski @ (k2_tarski @ X4 @ k1_xboole_0)) = (X4))),
% 0.39/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['23', '26'])).
% 0.39/0.61  thf('28', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.61  thf(t100_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X2 @ X3)
% 0.39/0.61           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['27', '30'])).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X2 @ X3)
% 0.39/0.61           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.39/0.61           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.61  thf('35', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.61  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.39/0.61  thf('37', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ X9 @ X10)
% 0.39/0.61           = (k5_xboole_0 @ X9 @ 
% 0.39/0.61              (k5_xboole_0 @ X10 @ (k3_tarski @ (k2_tarski @ X9 @ X10)))))),
% 0.39/0.61      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((k3_xboole_0 @ X0 @ X0)
% 0.39/0.61           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.39/0.61  thf('40', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.61  thf('41', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.61  thf('42', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['36', '42'])).
% 0.39/0.61  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['33', '43'])).
% 0.39/0.61  thf('45', plain, (((sk_A) != (sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['8', '44'])).
% 0.39/0.61  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
