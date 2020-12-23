%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.diwzZl2SI8

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:10 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 226 expanded)
%              Number of leaves         :   22 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          :  485 (1472 expanded)
%              Number of equality atoms :   64 ( 197 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X35 != X34 )
      | ( r2_hidden @ X35 @ X36 )
      | ( X36
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X34: $i] :
      ( r2_hidden @ X34 @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','25'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('43',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('45',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ( X37 = X34 )
      | ( X36
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('49',plain,(
    ! [X34: $i,X37: $i] :
      ( ( X37 = X34 )
      | ~ ( r2_hidden @ X37 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.diwzZl2SI8
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:04:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 556 iterations in 0.219s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(d1_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.67         (((X35) != (X34))
% 0.45/0.67          | (r2_hidden @ X35 @ X36)
% 0.45/0.67          | ((X36) != (k1_tarski @ X34)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.67  thf('1', plain, (![X34 : $i]: (r2_hidden @ X34 @ (k1_tarski @ X34))),
% 0.45/0.67      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.67  thf(t13_zfmisc_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.67         ( k1_tarski @ A ) ) =>
% 0.45/0.67       ( ( A ) = ( B ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.67            ( k1_tarski @ A ) ) =>
% 0.45/0.67          ( ( A ) = ( B ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.45/0.67         = (k1_tarski @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t98_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ X20 @ X21)
% 0.45/0.67           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.67  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.67  thf('4', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.45/0.67      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.67  thf(t100_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X9 @ X10)
% 0.45/0.67           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf(t91_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.67       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.45/0.67           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.67  thf('9', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.67  thf(t28_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i]:
% 0.45/0.67         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X9 @ X10)
% 0.45/0.67           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.45/0.67  thf(t5_boole, axiom,
% 0.45/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.67  thf('16', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.67  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.67  thf(t48_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.67           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.67  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ X20 @ X21)
% 0.45/0.67           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.45/0.67      inference('sup+', [status(thm)], ['21', '24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.45/0.67      inference('demod', [status(thm)], ['8', '25'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.45/0.67      inference('demod', [status(thm)], ['8', '25'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['27', '28'])).
% 0.45/0.67  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.67  thf('31', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.45/0.67      inference('sup+', [status(thm)], ['30', '31'])).
% 0.45/0.67  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '32'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.45/0.67      inference('demod', [status(thm)], ['26', '33'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['3', '34'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.45/0.67         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['2', '35'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.67           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.45/0.67         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      (((k1_tarski @ sk_B)
% 0.45/0.67         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['41', '42'])).
% 0.45/0.67  thf(d4_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.45/0.67       ( ![D:$i]:
% 0.45/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.67           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X6 @ X5)
% 0.45/0.67          | (r2_hidden @ X6 @ X4)
% 0.45/0.67          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.45/0.67         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['44'])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.45/0.67          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['43', '45'])).
% 0.45/0.67  thf('47', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '46'])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X37 @ X36)
% 0.45/0.67          | ((X37) = (X34))
% 0.45/0.67          | ((X36) != (k1_tarski @ X34)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      (![X34 : $i, X37 : $i]:
% 0.45/0.67         (((X37) = (X34)) | ~ (r2_hidden @ X37 @ (k1_tarski @ X34)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['48'])).
% 0.45/0.67  thf('50', plain, (((sk_B) = (sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['47', '49'])).
% 0.45/0.67  thf('51', plain, (((sk_A) != (sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('52', plain, ($false),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
