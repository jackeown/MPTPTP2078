%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.paAgydr7ff

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 189 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          :  457 (1269 expanded)
%              Number of equality atoms :   33 ( 114 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( r1_xboole_0 @ X24 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X17 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('28',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','28'])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['2','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( r1_xboole_0 @ X24 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['46','49'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('52',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['43','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.paAgydr7ff
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:38:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 158 iterations in 0.057s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(t106_xboole_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.52       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.52          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf(t36_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.21/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.52  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t28_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf(t100_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.52           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.21/0.52         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t39_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.21/0.52           = (k2_xboole_0 @ X14 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.52  thf(t1_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('10', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.52  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '11'])).
% 0.21/0.52  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.21/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.52  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.52  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.52           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.21/0.52         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.21/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.52  thf('23', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A)),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf(t85_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X24 @ X25)
% 0.21/0.52          | (r1_xboole_0 @ X24 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ (k4_xboole_0 @ X0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ (k5_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['20', '25'])).
% 0.21/0.52  thf(t66_xboole_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X17 : $i]: (((X17) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X17 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.52  thf('28', plain, (((k5_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.21/0.52           = (k2_xboole_0 @ X14 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ k1_xboole_0)
% 0.21/0.52         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.52  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.21/0.52         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.21/0.52  thf(t11_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)
% 0.21/0.52          | (r1_tarski @ sk_A @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('40', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('42', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 0.21/0.52  thf('44', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X24 @ X25)
% 0.21/0.52          | (r1_xboole_0 @ X24 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.21/0.52         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.21/0.52  thf(t70_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X18 @ X19)
% 0.21/0.52          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.21/0.52          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.52  thf('52', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf('53', plain, ($false), inference('demod', [status(thm)], ['43', '52'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
