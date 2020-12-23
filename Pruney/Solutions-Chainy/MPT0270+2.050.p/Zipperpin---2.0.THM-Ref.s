%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kTROmVisT0

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 208 expanded)
%              Number of leaves         :   22 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  496 (1522 expanded)
%              Number of equality atoms :   58 ( 184 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('24',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','29'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('31',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50 != X49 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X49 ) )
       != ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('32',plain,(
    ! [X49: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X49 ) )
     != ( k1_tarski @ X49 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('34',plain,(
    ! [X49: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X49 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','36'])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('39',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf('44',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','36','43'])).

thf('45',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['38','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kTROmVisT0
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:50:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 183 iterations in 0.071s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(t67_zfmisc_1, conjecture,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.55       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i]:
% 0.22/0.55        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.55          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.22/0.55        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.55       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.22/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf(t48_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.55           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.22/0.55          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.22/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.22/0.55          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.22/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf(t17_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.22/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.55  thf(t3_xboole_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf(t100_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.55           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf(t5_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.55  thf('15', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.55  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.55           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.22/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['7', '20'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ sk_B)
% 0.22/0.55        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['22'])).
% 0.22/0.55  thf(l1_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X44 : $i, X46 : $i]:
% 0.22/0.55         ((r1_tarski @ (k1_tarski @ X44) @ X46) | ~ (r2_hidden @ X44 @ X46))),
% 0.22/0.55      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf(t28_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i]:
% 0.22/0.55         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      ((((k1_xboole_0) = (k1_tarski @ sk_A)))
% 0.22/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.22/0.55             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['21', '29'])).
% 0.22/0.55  thf(t20_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.55         ( k1_tarski @ A ) ) <=>
% 0.22/0.55       ( ( A ) != ( B ) ) ))).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (![X49 : $i, X50 : $i]:
% 0.22/0.55         (((X50) != (X49))
% 0.22/0.55          | ((k4_xboole_0 @ (k1_tarski @ X50) @ (k1_tarski @ X49))
% 0.22/0.55              != (k1_tarski @ X50)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (![X49 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X49))
% 0.22/0.55           != (k1_tarski @ X49))),
% 0.22/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.55  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('34', plain, (![X49 : $i]: ((k1_xboole_0) != (k1_tarski @ X49))),
% 0.22/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.22/0.56             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['30', '34'])).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.22/0.56       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.56  thf('37', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['2', '36'])).
% 0.22/0.56  thf('38', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 0.22/0.56  thf(l27_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (![X47 : $i, X48 : $i]:
% 0.22/0.56         ((r1_xboole_0 @ (k1_tarski @ X47) @ X48) | (r2_hidden @ X47 @ X48))),
% 0.22/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.22/0.56  thf(t83_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      (![X13 : $i, X14 : $i]:
% 0.22/0.56         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.22/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((r2_hidden @ X1 @ X0)
% 0.22/0.56          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.56  thf('42', plain,
% 0.22/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.22/0.56         <= (~
% 0.22/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.56      inference('split', [status(esa)], ['22'])).
% 0.22/0.56  thf('43', plain,
% 0.22/0.56      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.22/0.56       ((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.56      inference('split', [status(esa)], ['22'])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['2', '36', '43'])).
% 0.22/0.56  thf('45', plain,
% 0.22/0.56      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['42', '44'])).
% 0.22/0.56  thf('46', plain,
% 0.22/0.56      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['41', '45'])).
% 0.22/0.56  thf('47', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.56      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.56  thf('48', plain, ($false), inference('demod', [status(thm)], ['38', '47'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
