%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D00x3FXo8D

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 179 expanded)
%              Number of leaves         :   16 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  537 (1572 expanded)
%              Number of equality atoms :   61 ( 185 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_C @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_C @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ sk_C )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['4','5'])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_D ) )
      = ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_D ) )
      = ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_D ) @ sk_C )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','28','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_C ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('51',plain,(
    sk_B = sk_C ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D00x3FXo8D
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 84 iterations in 0.077s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(t72_xboole_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.20/0.53         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.20/0.53       ( ( C ) = ( B ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.20/0.53            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.20/0.53          ( ( C ) = ( B ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.20/0.53  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d7_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.53  thf('2', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf('4', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t51_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.20/0.53       ( A ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.53           = (X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf(t40_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 0.20/0.53           = (k4_xboole_0 @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.20/0.53           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.20/0.53         = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D) @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.20/0.53  thf('11', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.53  thf('13', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.53           = (X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(t41_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.53       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.53           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.20/0.53           (k4_xboole_0 @ sk_C @ sk_A)) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 0.20/0.53         (k4_xboole_0 @ sk_C @ sk_A))
% 0.20/0.53         = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D) @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['10', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.20/0.53           (k4_xboole_0 @ sk_C @ sk_A)) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.53           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.20/0.53           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ sk_C)
% 0.20/0.53           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.20/0.53           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ sk_C)
% 0.20/0.53           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.20/0.53           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.20/0.53         = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.53           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.20/0.53           (k4_xboole_0 @ sk_B @ sk_D)) = (k4_xboole_0 @ X0 @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C @ k1_xboole_0) @ 
% 0.20/0.53         (k4_xboole_0 @ sk_B @ sk_D))
% 0.20/0.53         = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['31', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.20/0.53           (k4_xboole_0 @ sk_B @ sk_D)) = (k4_xboole_0 @ X0 @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 0.20/0.53           = (k4_xboole_0 @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.20/0.53         = (k4_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.53      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ sk_C)
% 0.20/0.53           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_D) @ sk_C)
% 0.20/0.53         = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.53            sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ sk_C)
% 0.20/0.53           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 0.20/0.53           = (k4_xboole_0 @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 0.20/0.53         = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_C @ sk_B)
% 0.20/0.53         = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '36', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_B @ sk_C) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['18', '19', '28', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.53           = (X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((k2_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_B) @ 
% 0.20/0.53         (k4_xboole_0 @ sk_B @ sk_C)) = (sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.53           = (X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.53  thf('51', plain, (((sk_B) = (sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.53  thf('52', plain, (((sk_C) != (sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('53', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
