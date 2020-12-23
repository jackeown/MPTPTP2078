%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.460YBvJcsx

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 201 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  462 (2030 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

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
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','23'])).

thf('25',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','23','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('39',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','14','23','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['25','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.460YBvJcsx
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 77 iterations in 0.042s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(t70_xboole_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.50               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.50          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.50               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 0.20/0.50        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.20/0.50        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.50         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.50       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.20/0.50        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf(t7_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('6', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.50  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(t64_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.20/0.50         ( r1_xboole_0 @ B @ D ) ) =>
% 0.20/0.50       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X9 @ X10)
% 0.20/0.50          | ~ (r1_tarski @ X9 @ X11)
% 0.20/0.50          | ~ (r1_tarski @ X10 @ X12)
% 0.20/0.50          | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ X2 @ X1)
% 0.20/0.50          | (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X2 @ X1)
% 0.20/0.50          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.20/0.50       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ X2 @ X1)
% 0.20/0.50          | (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X2 @ X0)
% 0.20/0.50          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_C))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.20/0.50       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '14', '23'])).
% 0.20/0.50  thf('25', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf(d7_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.20/0.50       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('30', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '14', '23', '29'])).
% 0.20/0.50  thf('31', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.20/0.50        | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf(t23_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.20/0.50       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 0.20/0.50           = (k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.20/0.50            = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))))
% 0.20/0.50         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 0.20/0.50       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['32'])).
% 0.20/0.50  thf('39', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '14', '23', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.20/0.50           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X2 : $i, X4 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))
% 0.20/0.50            != (k1_xboole_0))
% 0.20/0.50          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '42'])).
% 0.20/0.50  thf('44', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.50  thf('47', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.50  thf('48', plain, ($false), inference('demod', [status(thm)], ['25', '47'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
