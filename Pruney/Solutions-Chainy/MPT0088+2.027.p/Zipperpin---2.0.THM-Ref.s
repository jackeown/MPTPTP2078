%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3aB3QTY8IF

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:38 EST 2020

% Result     : Theorem 9.51s
% Output     : Refutation 9.51s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 142 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  568 (1054 expanded)
%              Number of equality atoms :   62 ( 124 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,
    ( sk_A
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','31'])).

thf('33',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ sk_A ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ sk_A ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['9','53'])).

thf('55',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('56',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('58',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3aB3QTY8IF
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:38:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 9.51/9.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.51/9.72  % Solved by: fo/fo7.sh
% 9.51/9.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.51/9.72  % done 6577 iterations in 9.285s
% 9.51/9.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.51/9.72  % SZS output start Refutation
% 9.51/9.72  thf(sk_B_type, type, sk_B: $i).
% 9.51/9.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.51/9.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.51/9.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.51/9.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.51/9.72  thf(sk_C_type, type, sk_C: $i).
% 9.51/9.72  thf(sk_A_type, type, sk_A: $i).
% 9.51/9.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.51/9.72  thf(t81_xboole_1, conjecture,
% 9.51/9.72    (![A:$i,B:$i,C:$i]:
% 9.51/9.72     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 9.51/9.72       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 9.51/9.72  thf(zf_stmt_0, negated_conjecture,
% 9.51/9.72    (~( ![A:$i,B:$i,C:$i]:
% 9.51/9.72        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 9.51/9.72          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 9.51/9.72    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 9.51/9.72  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 9.51/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.72  thf(t3_boole, axiom,
% 9.51/9.72    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.51/9.72  thf('1', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 9.51/9.72      inference('cnf', [status(esa)], [t3_boole])).
% 9.51/9.72  thf(t48_xboole_1, axiom,
% 9.51/9.72    (![A:$i,B:$i]:
% 9.51/9.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.51/9.72  thf('2', plain,
% 9.51/9.72      (![X10 : $i, X11 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 9.51/9.72           = (k3_xboole_0 @ X10 @ X11))),
% 9.51/9.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.51/9.72  thf('3', plain,
% 9.51/9.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 9.51/9.72      inference('sup+', [status(thm)], ['1', '2'])).
% 9.51/9.72  thf(t2_boole, axiom,
% 9.51/9.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 9.51/9.72  thf('4', plain,
% 9.51/9.72      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 9.51/9.72      inference('cnf', [status(esa)], [t2_boole])).
% 9.51/9.72  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.51/9.72      inference('demod', [status(thm)], ['3', '4'])).
% 9.51/9.72  thf(t41_xboole_1, axiom,
% 9.51/9.72    (![A:$i,B:$i,C:$i]:
% 9.51/9.72     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 9.51/9.72       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.51/9.72  thf('6', plain,
% 9.51/9.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 9.51/9.72           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 9.51/9.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.51/9.72  thf('7', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         ((k1_xboole_0)
% 9.51/9.72           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.51/9.72      inference('sup+', [status(thm)], ['5', '6'])).
% 9.51/9.72  thf(t39_xboole_1, axiom,
% 9.51/9.72    (![A:$i,B:$i]:
% 9.51/9.72     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.51/9.72  thf('8', plain,
% 9.51/9.72      (![X4 : $i, X5 : $i]:
% 9.51/9.72         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 9.51/9.72           = (k2_xboole_0 @ X4 @ X5))),
% 9.51/9.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.51/9.72  thf('9', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.51/9.72      inference('demod', [status(thm)], ['7', '8'])).
% 9.51/9.72  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.51/9.72      inference('demod', [status(thm)], ['3', '4'])).
% 9.51/9.72  thf('11', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 9.51/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.72  thf(d7_xboole_0, axiom,
% 9.51/9.72    (![A:$i,B:$i]:
% 9.51/9.72     ( ( r1_xboole_0 @ A @ B ) <=>
% 9.51/9.72       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 9.51/9.72  thf('12', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 9.51/9.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.51/9.72  thf('13', plain,
% 9.51/9.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 9.51/9.72      inference('sup-', [status(thm)], ['11', '12'])).
% 9.51/9.72  thf(t52_xboole_1, axiom,
% 9.51/9.72    (![A:$i,B:$i,C:$i]:
% 9.51/9.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 9.51/9.72       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 9.51/9.72  thf('14', plain,
% 9.51/9.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 9.51/9.72              (k3_xboole_0 @ X12 @ X14)))),
% 9.51/9.72      inference('cnf', [status(esa)], [t52_xboole_1])).
% 9.51/9.72  thf('15', plain,
% 9.51/9.72      (![X0 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ sk_A @ 
% 9.51/9.72           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 9.51/9.72      inference('sup+', [status(thm)], ['13', '14'])).
% 9.51/9.72  thf('16', plain,
% 9.51/9.72      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 9.51/9.72         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 9.51/9.72            k1_xboole_0))),
% 9.51/9.72      inference('sup+', [status(thm)], ['10', '15'])).
% 9.51/9.72  thf('17', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 9.51/9.72      inference('cnf', [status(esa)], [t3_boole])).
% 9.51/9.72  thf('18', plain,
% 9.51/9.72      (((sk_A)
% 9.51/9.72         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 9.51/9.72            k1_xboole_0))),
% 9.51/9.72      inference('demod', [status(thm)], ['16', '17'])).
% 9.51/9.72  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.51/9.72      inference('demod', [status(thm)], ['3', '4'])).
% 9.51/9.72  thf('20', plain,
% 9.51/9.72      (![X4 : $i, X5 : $i]:
% 9.51/9.72         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 9.51/9.72           = (k2_xboole_0 @ X4 @ X5))),
% 9.51/9.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.51/9.72  thf('21', plain,
% 9.51/9.72      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 9.51/9.72      inference('sup+', [status(thm)], ['19', '20'])).
% 9.51/9.72  thf('22', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 9.51/9.72      inference('cnf', [status(esa)], [t3_boole])).
% 9.51/9.72  thf('23', plain,
% 9.51/9.72      (![X10 : $i, X11 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 9.51/9.72           = (k3_xboole_0 @ X10 @ X11))),
% 9.51/9.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.51/9.72  thf('24', plain,
% 9.51/9.72      (![X4 : $i, X5 : $i]:
% 9.51/9.72         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 9.51/9.72           = (k2_xboole_0 @ X4 @ X5))),
% 9.51/9.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.51/9.72  thf('25', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 9.51/9.72      inference('sup+', [status(thm)], ['23', '24'])).
% 9.51/9.72  thf('26', plain,
% 9.51/9.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 9.51/9.72              (k3_xboole_0 @ X12 @ X14)))),
% 9.51/9.72      inference('cnf', [status(esa)], [t52_xboole_1])).
% 9.51/9.72  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.51/9.72      inference('demod', [status(thm)], ['3', '4'])).
% 9.51/9.72  thf('28', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 9.51/9.72      inference('demod', [status(thm)], ['25', '26', '27'])).
% 9.51/9.72  thf('29', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 9.51/9.72      inference('cnf', [status(esa)], [t3_boole])).
% 9.51/9.72  thf('30', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 9.51/9.72      inference('demod', [status(thm)], ['28', '29'])).
% 9.51/9.72  thf('31', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 9.51/9.72      inference('sup+', [status(thm)], ['22', '30'])).
% 9.51/9.72  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.51/9.72      inference('demod', [status(thm)], ['21', '31'])).
% 9.51/9.72  thf('33', plain,
% 9.51/9.72      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 9.51/9.72      inference('demod', [status(thm)], ['18', '32'])).
% 9.51/9.72  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.51/9.72      inference('demod', [status(thm)], ['3', '4'])).
% 9.51/9.72  thf('35', plain,
% 9.51/9.72      (![X10 : $i, X11 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 9.51/9.72           = (k3_xboole_0 @ X10 @ X11))),
% 9.51/9.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.51/9.72  thf('36', plain,
% 9.51/9.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 9.51/9.72      inference('sup+', [status(thm)], ['34', '35'])).
% 9.51/9.72  thf('37', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 9.51/9.72      inference('cnf', [status(esa)], [t3_boole])).
% 9.51/9.72  thf('38', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 9.51/9.72      inference('demod', [status(thm)], ['36', '37'])).
% 9.51/9.72  thf('39', plain,
% 9.51/9.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 9.51/9.72              (k3_xboole_0 @ X12 @ X14)))),
% 9.51/9.72      inference('cnf', [status(esa)], [t52_xboole_1])).
% 9.51/9.72  thf('40', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 9.51/9.72      inference('sup+', [status(thm)], ['38', '39'])).
% 9.51/9.72  thf('41', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 9.51/9.72      inference('demod', [status(thm)], ['28', '29'])).
% 9.51/9.72  thf('42', plain,
% 9.51/9.72      (![X0 : $i, X1 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 9.51/9.72      inference('demod', [status(thm)], ['40', '41'])).
% 9.51/9.72  thf('43', plain,
% 9.51/9.72      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 9.51/9.72         = (k4_xboole_0 @ sk_B @ sk_C))),
% 9.51/9.72      inference('sup+', [status(thm)], ['33', '42'])).
% 9.51/9.72  thf('44', plain,
% 9.51/9.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 9.51/9.72           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 9.51/9.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.51/9.72  thf('45', plain,
% 9.51/9.72      (((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A))
% 9.51/9.72         = (k4_xboole_0 @ sk_B @ sk_C))),
% 9.51/9.72      inference('demod', [status(thm)], ['43', '44'])).
% 9.51/9.72  thf('46', plain,
% 9.51/9.72      (![X10 : $i, X11 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 9.51/9.72           = (k3_xboole_0 @ X10 @ X11))),
% 9.51/9.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.51/9.72  thf('47', plain,
% 9.51/9.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C))
% 9.51/9.72         = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A)))),
% 9.51/9.72      inference('sup+', [status(thm)], ['45', '46'])).
% 9.51/9.72  thf('48', plain,
% 9.51/9.72      (![X10 : $i, X11 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 9.51/9.72           = (k3_xboole_0 @ X10 @ X11))),
% 9.51/9.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.51/9.72  thf('49', plain,
% 9.51/9.72      (((k3_xboole_0 @ sk_B @ sk_C)
% 9.51/9.72         = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A)))),
% 9.51/9.72      inference('demod', [status(thm)], ['47', '48'])).
% 9.51/9.72  thf('50', plain,
% 9.51/9.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 9.51/9.72              (k3_xboole_0 @ X12 @ X14)))),
% 9.51/9.72      inference('cnf', [status(esa)], [t52_xboole_1])).
% 9.51/9.72  thf('51', plain,
% 9.51/9.72      (![X0 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ sk_B @ 
% 9.51/9.72           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_C @ sk_A)))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 9.51/9.72              (k3_xboole_0 @ sk_B @ sk_C)))),
% 9.51/9.72      inference('sup+', [status(thm)], ['49', '50'])).
% 9.51/9.72  thf('52', plain,
% 9.51/9.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 9.51/9.72           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 9.51/9.72              (k3_xboole_0 @ X12 @ X14)))),
% 9.51/9.72      inference('cnf', [status(esa)], [t52_xboole_1])).
% 9.51/9.72  thf('53', plain,
% 9.51/9.72      (![X0 : $i]:
% 9.51/9.72         ((k4_xboole_0 @ sk_B @ 
% 9.51/9.72           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_C @ sk_A)))
% 9.51/9.72           = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C)))),
% 9.51/9.72      inference('demod', [status(thm)], ['51', '52'])).
% 9.51/9.72  thf('54', plain,
% 9.51/9.72      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 9.51/9.72         = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 9.51/9.72      inference('sup+', [status(thm)], ['9', '53'])).
% 9.51/9.72  thf('55', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 9.51/9.72      inference('cnf', [status(esa)], [t3_boole])).
% 9.51/9.72  thf('56', plain,
% 9.51/9.72      (((sk_B) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 9.51/9.72      inference('demod', [status(thm)], ['54', '55'])).
% 9.51/9.72  thf(t79_xboole_1, axiom,
% 9.51/9.72    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 9.51/9.72  thf('57', plain,
% 9.51/9.72      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 9.51/9.72      inference('cnf', [status(esa)], [t79_xboole_1])).
% 9.51/9.72  thf('58', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 9.51/9.72      inference('sup+', [status(thm)], ['56', '57'])).
% 9.51/9.72  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 9.51/9.72  
% 9.51/9.72  % SZS output end Refutation
% 9.51/9.72  
% 9.55/9.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
