%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pdA0CTB2tw

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:08 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 183 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  415 (1364 expanded)
%              Number of equality atoms :   58 ( 183 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X45: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','14','15'])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['23','32','33'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('37',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41
        = ( k1_tarski @ X40 ) )
      | ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ X41 @ ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pdA0CTB2tw
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.63  % Solved by: fo/fo7.sh
% 0.36/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.63  % done 419 iterations in 0.175s
% 0.36/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.63  % SZS output start Refutation
% 0.36/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.63  thf(t66_zfmisc_1, conjecture,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.36/0.63          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.36/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.63    (~( ![A:$i,B:$i]:
% 0.36/0.63        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.36/0.63             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.36/0.63    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.36/0.63  thf('0', plain,
% 0.36/0.63      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf(t95_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( k3_xboole_0 @ A @ B ) =
% 0.36/0.63       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.36/0.63  thf('1', plain,
% 0.36/0.63      (![X10 : $i, X11 : $i]:
% 0.36/0.63         ((k3_xboole_0 @ X10 @ X11)
% 0.36/0.63           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.36/0.63              (k2_xboole_0 @ X10 @ X11)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.36/0.63  thf(t91_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i]:
% 0.36/0.63     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.63       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.63  thf('2', plain,
% 0.36/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.36/0.63           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.63  thf('3', plain,
% 0.36/0.63      (![X10 : $i, X11 : $i]:
% 0.36/0.63         ((k3_xboole_0 @ X10 @ X11)
% 0.36/0.63           = (k5_xboole_0 @ X10 @ 
% 0.36/0.63              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 0.36/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.63  thf(t92_xboole_1, axiom,
% 0.36/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.63  thf('4', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.36/0.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.63  thf('5', plain,
% 0.36/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.36/0.63           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.63  thf('6', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.63           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.36/0.63  thf('7', plain,
% 0.36/0.63      (![X10 : $i, X11 : $i]:
% 0.36/0.63         ((k3_xboole_0 @ X10 @ X11)
% 0.36/0.63           = (k5_xboole_0 @ X10 @ 
% 0.36/0.63              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 0.36/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.63  thf('8', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.63           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.36/0.63  thf('9', plain,
% 0.36/0.63      (![X0 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.36/0.63           = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.36/0.63  thf(t69_enumset1, axiom,
% 0.36/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.63  thf('10', plain,
% 0.36/0.63      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.36/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.63  thf(t31_zfmisc_1, axiom,
% 0.36/0.63    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.36/0.63  thf('11', plain, (![X45 : $i]: ((k3_tarski @ (k1_tarski @ X45)) = (X45))),
% 0.36/0.63      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.36/0.63  thf('12', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.36/0.63      inference('sup+', [status(thm)], ['10', '11'])).
% 0.36/0.63  thf(l51_zfmisc_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.63  thf('13', plain,
% 0.36/0.63      (![X43 : $i, X44 : $i]:
% 0.36/0.63         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.36/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.63  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.63  thf(idempotence_k3_xboole_0, axiom,
% 0.36/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.63  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.63      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.36/0.63  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.63      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.36/0.63  thf('17', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('demod', [status(thm)], ['6', '16'])).
% 0.36/0.63  thf('18', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.36/0.63           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['3', '17'])).
% 0.36/0.63  thf(t100_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.63  thf('19', plain,
% 0.36/0.63      (![X1 : $i, X2 : $i]:
% 0.36/0.63         ((k4_xboole_0 @ X1 @ X2)
% 0.36/0.63           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.63  thf('20', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.36/0.63           = (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.63      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.63  thf('21', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('demod', [status(thm)], ['6', '16'])).
% 0.36/0.63  thf('22', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ X1 @ X0)
% 0.36/0.63           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.36/0.63  thf('23', plain,
% 0.36/0.63      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.63         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.36/0.63      inference('sup+', [status(thm)], ['0', '22'])).
% 0.36/0.63  thf('24', plain,
% 0.36/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.36/0.63           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.63  thf('25', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.36/0.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.63  thf('26', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.36/0.63           = (k1_xboole_0))),
% 0.36/0.63      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.63  thf('27', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('demod', [status(thm)], ['6', '16'])).
% 0.36/0.63  thf('28', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.36/0.63           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.36/0.63      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.63  thf(t5_boole, axiom,
% 0.36/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.63  thf('29', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.36/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.63  thf('30', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.36/0.63      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.63  thf('31', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('demod', [status(thm)], ['6', '16'])).
% 0.36/0.63  thf('32', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.36/0.63      inference('sup+', [status(thm)], ['30', '31'])).
% 0.36/0.63  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.63      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.36/0.63  thf('34', plain,
% 0.36/0.63      (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.36/0.63      inference('demod', [status(thm)], ['23', '32', '33'])).
% 0.36/0.63  thf(t7_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.63  thf('35', plain,
% 0.36/0.63      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.36/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.63  thf('36', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.36/0.63      inference('sup+', [status(thm)], ['34', '35'])).
% 0.36/0.63  thf(l3_zfmisc_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.36/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.36/0.63  thf('37', plain,
% 0.36/0.63      (![X40 : $i, X41 : $i]:
% 0.36/0.63         (((X41) = (k1_tarski @ X40))
% 0.36/0.63          | ((X41) = (k1_xboole_0))
% 0.36/0.63          | ~ (r1_tarski @ X41 @ (k1_tarski @ X40)))),
% 0.36/0.63      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.36/0.63  thf('38', plain,
% 0.36/0.63      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.63  thf('39', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('41', plain, ($false),
% 0.36/0.63      inference('simplify_reflect-', [status(thm)], ['38', '39', '40'])).
% 0.36/0.63  
% 0.36/0.63  % SZS output end Refutation
% 0.36/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
