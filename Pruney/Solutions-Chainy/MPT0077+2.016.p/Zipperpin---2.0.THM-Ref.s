%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rQsM8ZJ0YP

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:51 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 212 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  549 (2128 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','14','25','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('39',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('45',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','25','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['43','45'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['27','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rQsM8ZJ0YP
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.24/1.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.24/1.45  % Solved by: fo/fo7.sh
% 1.24/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.24/1.45  % done 1532 iterations in 0.993s
% 1.24/1.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.24/1.45  % SZS output start Refutation
% 1.24/1.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.24/1.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.24/1.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.24/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.24/1.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.24/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.24/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.24/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.24/1.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.24/1.45  thf(t70_xboole_1, conjecture,
% 1.24/1.45    (![A:$i,B:$i,C:$i]:
% 1.24/1.45     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.24/1.45            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.24/1.45       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.24/1.45            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.24/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.24/1.45    (~( ![A:$i,B:$i,C:$i]:
% 1.24/1.45        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.24/1.45               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.24/1.45          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.24/1.45               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 1.24/1.45    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 1.24/1.45  thf('0', plain,
% 1.24/1.45      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 1.24/1.45        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 1.24/1.45        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.24/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.45  thf('1', plain,
% 1.24/1.45      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.24/1.45         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.24/1.45      inference('split', [status(esa)], ['0'])).
% 1.24/1.45  thf('2', plain,
% 1.24/1.45      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.24/1.45       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 1.24/1.45      inference('split', [status(esa)], ['0'])).
% 1.24/1.45  thf('3', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.24/1.45        | (r1_xboole_0 @ sk_A @ sk_B))),
% 1.24/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.45  thf('4', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.24/1.45      inference('split', [status(esa)], ['3'])).
% 1.24/1.45  thf(symmetry_r1_xboole_0, axiom,
% 1.24/1.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.24/1.45  thf('5', plain,
% 1.24/1.45      (![X5 : $i, X6 : $i]:
% 1.24/1.45         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.24/1.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.24/1.45  thf('6', plain,
% 1.24/1.45      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.24/1.45      inference('sup-', [status(thm)], ['4', '5'])).
% 1.24/1.45  thf(t7_xboole_1, axiom,
% 1.24/1.45    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.24/1.45  thf('7', plain,
% 1.24/1.45      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.24/1.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.24/1.45  thf(t63_xboole_1, axiom,
% 1.24/1.45    (![A:$i,B:$i,C:$i]:
% 1.24/1.45     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.24/1.45       ( r1_xboole_0 @ A @ C ) ))).
% 1.24/1.45  thf('8', plain,
% 1.24/1.45      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.24/1.45         (~ (r1_tarski @ X17 @ X18)
% 1.24/1.45          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.24/1.45          | (r1_xboole_0 @ X17 @ X19))),
% 1.24/1.45      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.24/1.45  thf('9', plain,
% 1.24/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.24/1.45         ((r1_xboole_0 @ X1 @ X2)
% 1.24/1.45          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.24/1.45      inference('sup-', [status(thm)], ['7', '8'])).
% 1.24/1.45  thf('10', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_B @ sk_A))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.24/1.45      inference('sup-', [status(thm)], ['6', '9'])).
% 1.24/1.45  thf('11', plain,
% 1.24/1.45      (![X5 : $i, X6 : $i]:
% 1.24/1.45         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.24/1.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.24/1.45  thf('12', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ sk_B))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.24/1.45      inference('sup-', [status(thm)], ['10', '11'])).
% 1.24/1.45  thf('13', plain,
% 1.24/1.45      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.24/1.45      inference('split', [status(esa)], ['0'])).
% 1.24/1.45  thf('14', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 1.24/1.45       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.24/1.45      inference('sup-', [status(thm)], ['12', '13'])).
% 1.24/1.45  thf('15', plain,
% 1.24/1.45      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.24/1.45      inference('sup-', [status(thm)], ['4', '5'])).
% 1.24/1.45  thf(commutativity_k2_xboole_0, axiom,
% 1.24/1.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.24/1.45  thf('16', plain,
% 1.24/1.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.24/1.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.24/1.45  thf('17', plain,
% 1.24/1.45      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.24/1.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.24/1.45  thf('18', plain,
% 1.24/1.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.24/1.45      inference('sup+', [status(thm)], ['16', '17'])).
% 1.24/1.45  thf('19', plain,
% 1.24/1.45      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.24/1.45         (~ (r1_tarski @ X17 @ X18)
% 1.24/1.45          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.24/1.45          | (r1_xboole_0 @ X17 @ X19))),
% 1.24/1.45      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.24/1.45  thf('20', plain,
% 1.24/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.24/1.45         ((r1_xboole_0 @ X0 @ X2)
% 1.24/1.45          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.24/1.45      inference('sup-', [status(thm)], ['18', '19'])).
% 1.24/1.45  thf('21', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_C @ sk_A))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.24/1.45      inference('sup-', [status(thm)], ['15', '20'])).
% 1.24/1.45  thf('22', plain,
% 1.24/1.45      (![X5 : $i, X6 : $i]:
% 1.24/1.45         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.24/1.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.24/1.45  thf('23', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ sk_C))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.24/1.45      inference('sup-', [status(thm)], ['21', '22'])).
% 1.24/1.45  thf('24', plain,
% 1.24/1.45      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.24/1.45      inference('split', [status(esa)], ['0'])).
% 1.24/1.45  thf('25', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 1.24/1.45       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.24/1.45      inference('sup-', [status(thm)], ['23', '24'])).
% 1.24/1.45  thf('26', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.24/1.45      inference('sat_resolution*', [status(thm)], ['2', '14', '25'])).
% 1.24/1.45  thf('27', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.24/1.45      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 1.24/1.45  thf('28', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.24/1.45        | (r1_xboole_0 @ sk_A @ sk_C))),
% 1.24/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.45  thf('29', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.24/1.45      inference('split', [status(esa)], ['28'])).
% 1.24/1.45  thf(d7_xboole_0, axiom,
% 1.24/1.45    (![A:$i,B:$i]:
% 1.24/1.45     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.24/1.45       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.24/1.45  thf('30', plain,
% 1.24/1.45      (![X2 : $i, X3 : $i]:
% 1.24/1.45         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.24/1.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.24/1.45  thf('31', plain,
% 1.24/1.45      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.24/1.45      inference('sup-', [status(thm)], ['29', '30'])).
% 1.24/1.45  thf('32', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 1.24/1.45       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.24/1.45      inference('split', [status(esa)], ['28'])).
% 1.24/1.45  thf('33', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 1.24/1.45      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '32'])).
% 1.24/1.45  thf('34', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.24/1.45      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 1.24/1.45  thf('35', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.24/1.45      inference('split', [status(esa)], ['3'])).
% 1.24/1.45  thf('36', plain,
% 1.24/1.45      (![X2 : $i, X3 : $i]:
% 1.24/1.45         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.24/1.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.24/1.45  thf('37', plain,
% 1.24/1.45      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.24/1.45      inference('sup-', [status(thm)], ['35', '36'])).
% 1.24/1.45  thf(t51_xboole_1, axiom,
% 1.24/1.45    (![A:$i,B:$i]:
% 1.24/1.45     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.24/1.45       ( A ) ))).
% 1.24/1.45  thf('38', plain,
% 1.24/1.45      (![X15 : $i, X16 : $i]:
% 1.24/1.45         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 1.24/1.45           = (X15))),
% 1.24/1.45      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.24/1.45  thf('39', plain,
% 1.24/1.45      ((((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A)))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.24/1.45      inference('sup+', [status(thm)], ['37', '38'])).
% 1.24/1.45  thf('40', plain,
% 1.24/1.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.24/1.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.24/1.45  thf(t1_boole, axiom,
% 1.24/1.45    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.24/1.45  thf('41', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.24/1.45      inference('cnf', [status(esa)], [t1_boole])).
% 1.24/1.45  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.24/1.45      inference('sup+', [status(thm)], ['40', '41'])).
% 1.24/1.45  thf('43', plain,
% 1.24/1.45      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 1.24/1.45         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.24/1.45      inference('demod', [status(thm)], ['39', '42'])).
% 1.24/1.45  thf('44', plain,
% 1.24/1.45      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 1.24/1.45       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.24/1.45      inference('split', [status(esa)], ['3'])).
% 1.24/1.45  thf('45', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 1.24/1.45      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '44'])).
% 1.24/1.45  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.24/1.45      inference('simpl_trail', [status(thm)], ['43', '45'])).
% 1.24/1.45  thf(t41_xboole_1, axiom,
% 1.24/1.45    (![A:$i,B:$i,C:$i]:
% 1.24/1.45     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.24/1.45       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.24/1.45  thf('47', plain,
% 1.24/1.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.24/1.45         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.24/1.45           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.24/1.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.24/1.45  thf(t48_xboole_1, axiom,
% 1.24/1.45    (![A:$i,B:$i]:
% 1.24/1.45     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.24/1.45  thf('48', plain,
% 1.24/1.45      (![X13 : $i, X14 : $i]:
% 1.24/1.45         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.24/1.45           = (k3_xboole_0 @ X13 @ X14))),
% 1.24/1.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.24/1.45  thf('49', plain,
% 1.24/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.24/1.45         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 1.24/1.45           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.24/1.45      inference('sup+', [status(thm)], ['47', '48'])).
% 1.24/1.45  thf('50', plain,
% 1.24/1.45      (![X0 : $i]:
% 1.24/1.45         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 1.24/1.45           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.24/1.45      inference('sup+', [status(thm)], ['46', '49'])).
% 1.24/1.45  thf('51', plain,
% 1.24/1.45      (![X13 : $i, X14 : $i]:
% 1.24/1.45         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.24/1.45           = (k3_xboole_0 @ X13 @ X14))),
% 1.24/1.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.24/1.45  thf('52', plain,
% 1.24/1.45      (![X0 : $i]:
% 1.24/1.45         ((k3_xboole_0 @ sk_A @ X0)
% 1.24/1.45           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.24/1.45      inference('demod', [status(thm)], ['50', '51'])).
% 1.24/1.45  thf('53', plain,
% 1.24/1.45      (![X2 : $i, X4 : $i]:
% 1.24/1.45         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.24/1.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.24/1.45  thf('54', plain,
% 1.24/1.45      (![X0 : $i]:
% 1.24/1.45         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 1.24/1.45          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.24/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.24/1.45  thf('55', plain,
% 1.24/1.45      ((((k1_xboole_0) != (k1_xboole_0))
% 1.24/1.45        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.24/1.45      inference('sup-', [status(thm)], ['34', '54'])).
% 1.24/1.45  thf('56', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.24/1.45      inference('simplify', [status(thm)], ['55'])).
% 1.24/1.45  thf('57', plain, ($false), inference('demod', [status(thm)], ['27', '56'])).
% 1.24/1.45  
% 1.24/1.45  % SZS output end Refutation
% 1.24/1.45  
% 1.29/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
