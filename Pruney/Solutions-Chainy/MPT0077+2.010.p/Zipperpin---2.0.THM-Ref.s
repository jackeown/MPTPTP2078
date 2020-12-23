%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xr26O0ijqg

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 232 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  567 (2508 expanded)
%              Number of equality atoms :   31 (  81 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( r1_xboole_0 @ X12 @ X14 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
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
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','32'])).

thf('34',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','32','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['39'])).

thf('48',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','14','32','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['34','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xr26O0ijqg
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:18:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 234 iterations in 0.120s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(t70_xboole_1, conjecture,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.22/0.55            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.22/0.55       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.22/0.55            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.55        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.22/0.55               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.22/0.55          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.22/0.55               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 0.22/0.55        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.22/0.55        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.22/0.55         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.22/0.55       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.22/0.55        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.22/0.55      inference('split', [status(esa)], ['3'])).
% 0.22/0.55  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i]:
% 0.22/0.55         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf(t7_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.55  thf(t63_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.55       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.55         (~ (r1_tarski @ X12 @ X13)
% 0.22/0.55          | ~ (r1_xboole_0 @ X13 @ X14)
% 0.22/0.55          | (r1_xboole_0 @ X12 @ X14))),
% 0.22/0.55      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((r1_xboole_0 @ X1 @ X2)
% 0.22/0.55          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.22/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_B @ sk_A))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i]:
% 0.22/0.55         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.22/0.55       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['3'])).
% 0.22/0.55  thf(d7_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X2 : $i, X3 : $i]:
% 0.22/0.55         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf(t23_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.22/0.55       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.22/0.55           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      ((![X0 : $i]:
% 0.22/0.55          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.22/0.55            = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.55  thf(t1_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.55  thf('21', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.55  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      ((![X0 : $i]:
% 0.22/0.55          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.22/0.55            = (k3_xboole_0 @ sk_A @ X0)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['19', '22'])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.22/0.55      inference('split', [status(esa)], ['3'])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X2 : $i, X3 : $i]:
% 0.22/0.55         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.22/0.55             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['23', '26'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (![X2 : $i, X4 : $i]:
% 0.22/0.55         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.22/0.55             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ sk_C))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 0.22/0.55             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.22/0.55       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.55  thf('33', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['2', '14', '32'])).
% 0.22/0.55  thf('34', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.22/0.55       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('split', [status(esa)], ['3'])).
% 0.22/0.55  thf('37', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['2', '14', '32', '36'])).
% 0.22/0.55  thf('38', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.22/0.55        | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.22/0.55      inference('split', [status(esa)], ['39'])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (![X2 : $i, X3 : $i]:
% 0.22/0.55         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.22/0.55           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      ((![X0 : $i]:
% 0.22/0.55          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.22/0.55            = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.55  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      ((![X0 : $i]:
% 0.22/0.55          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.22/0.55            = (k3_xboole_0 @ sk_A @ X0)))
% 0.22/0.55         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.22/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.22/0.55       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('split', [status(esa)], ['39'])).
% 0.22/0.55  thf('48', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['2', '14', '32', '47'])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.22/0.55           = (k3_xboole_0 @ sk_A @ X0))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['46', '48'])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      (![X2 : $i, X4 : $i]:
% 0.22/0.55         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.22/0.55          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.55        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['38', '51'])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.55        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('55', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.55      inference('simplify', [status(thm)], ['54'])).
% 0.22/0.55  thf('56', plain, ($false), inference('demod', [status(thm)], ['34', '55'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.41/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
