%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.64knWrMZMt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:56 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 105 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  420 ( 736 expanded)
%              Number of equality atoms :   50 (  85 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 != X52 )
      | ~ ( r2_hidden @ X50 @ ( k4_xboole_0 @ X51 @ ( k1_tarski @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X51: $i,X52: $i] :
      ~ ( r2_hidden @ X52 @ ( k4_xboole_0 @ X51 @ ( k1_tarski @ X52 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('12',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X45 ) @ X46 )
      | ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('22',plain,(
    ! [X49: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','19','28'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','9','37'])).

thf('39',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['11','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.64knWrMZMt
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.59  % Solved by: fo/fo7.sh
% 0.35/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.59  % done 361 iterations in 0.132s
% 0.35/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.59  % SZS output start Refutation
% 0.35/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.35/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.59  thf(t65_zfmisc_1, conjecture,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.35/0.59       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.59    (~( ![A:$i,B:$i]:
% 0.35/0.59        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.35/0.59          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.35/0.59    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.35/0.59  thf('0', plain,
% 0.35/0.59      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.35/0.59        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('1', plain,
% 0.35/0.59      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.35/0.59      inference('split', [status(esa)], ['0'])).
% 0.35/0.59  thf('2', plain,
% 0.35/0.59      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.35/0.59       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.35/0.59      inference('split', [status(esa)], ['0'])).
% 0.35/0.59  thf('3', plain,
% 0.35/0.59      (((r2_hidden @ sk_B @ sk_A)
% 0.35/0.59        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('4', plain,
% 0.35/0.59      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.35/0.59      inference('split', [status(esa)], ['3'])).
% 0.35/0.59  thf('5', plain,
% 0.35/0.59      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.35/0.59         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.35/0.59      inference('split', [status(esa)], ['0'])).
% 0.35/0.59  thf(t64_zfmisc_1, axiom,
% 0.35/0.59    (![A:$i,B:$i,C:$i]:
% 0.35/0.59     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.35/0.59       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.35/0.59  thf('6', plain,
% 0.35/0.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.35/0.59         (((X50) != (X52))
% 0.35/0.59          | ~ (r2_hidden @ X50 @ (k4_xboole_0 @ X51 @ (k1_tarski @ X52))))),
% 0.35/0.59      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.35/0.59  thf('7', plain,
% 0.35/0.59      (![X51 : $i, X52 : $i]:
% 0.35/0.59         ~ (r2_hidden @ X52 @ (k4_xboole_0 @ X51 @ (k1_tarski @ X52)))),
% 0.35/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.35/0.59  thf('8', plain,
% 0.35/0.59      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.35/0.59         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.35/0.59      inference('sup-', [status(thm)], ['5', '7'])).
% 0.35/0.59  thf('9', plain,
% 0.35/0.59      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.35/0.59       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.35/0.59      inference('sup-', [status(thm)], ['4', '8'])).
% 0.35/0.59  thf('10', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.35/0.59      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 0.35/0.59  thf('11', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.35/0.59      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.35/0.59  thf(l27_zfmisc_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.35/0.59  thf('12', plain,
% 0.35/0.59      (![X45 : $i, X46 : $i]:
% 0.35/0.59         ((r1_xboole_0 @ (k1_tarski @ X45) @ X46) | (r2_hidden @ X45 @ X46))),
% 0.35/0.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.35/0.59  thf(t83_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.59  thf('13', plain,
% 0.35/0.59      (![X14 : $i, X15 : $i]:
% 0.35/0.59         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.35/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.35/0.59  thf('14', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((r2_hidden @ X1 @ X0)
% 0.35/0.59          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.59  thf(t48_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.59  thf('15', plain,
% 0.35/0.59      (![X11 : $i, X12 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.35/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.35/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.59  thf('16', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.35/0.59            = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.35/0.59          | (r2_hidden @ X0 @ X1))),
% 0.35/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.35/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.35/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.35/0.59  thf('17', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.35/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.35/0.59  thf(t100_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.59  thf('18', plain,
% 0.35/0.59      (![X3 : $i, X4 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X3 @ X4)
% 0.35/0.59           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.59  thf('19', plain,
% 0.35/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.35/0.59  thf('20', plain,
% 0.35/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.35/0.59  thf(t69_enumset1, axiom,
% 0.35/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.59  thf('21', plain,
% 0.35/0.59      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.35/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.59  thf(t31_zfmisc_1, axiom,
% 0.35/0.59    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.35/0.59  thf('22', plain, (![X49 : $i]: ((k3_tarski @ (k1_tarski @ X49)) = (X49))),
% 0.35/0.59      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.35/0.59  thf('23', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.59  thf(l51_zfmisc_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.59  thf('24', plain,
% 0.35/0.59      (![X47 : $i, X48 : $i]:
% 0.35/0.59         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.35/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.59  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.59  thf(t46_xboole_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.35/0.59  thf('26', plain,
% 0.35/0.59      (![X9 : $i, X10 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 0.35/0.59      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.35/0.59  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['25', '26'])).
% 0.35/0.59  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['20', '27'])).
% 0.35/0.59  thf('29', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.35/0.59          | (r2_hidden @ X0 @ X1))),
% 0.35/0.59      inference('demod', [status(thm)], ['16', '19', '28'])).
% 0.35/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.35/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.35/0.59  thf('30', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.59  thf('31', plain,
% 0.35/0.59      (![X3 : $i, X4 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X3 @ X4)
% 0.35/0.59           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.59  thf('32', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.35/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.35/0.59  thf('33', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.35/0.59            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.35/0.59          | (r2_hidden @ X1 @ X0))),
% 0.35/0.59      inference('sup+', [status(thm)], ['29', '32'])).
% 0.35/0.59  thf(t5_boole, axiom,
% 0.35/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.59  thf('34', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.35/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.59  thf('35', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.35/0.59          | (r2_hidden @ X1 @ X0))),
% 0.35/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.59  thf('36', plain,
% 0.35/0.59      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.35/0.59         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.35/0.59      inference('split', [status(esa)], ['3'])).
% 0.35/0.59  thf('37', plain,
% 0.35/0.59      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.35/0.59       ((r2_hidden @ sk_B @ sk_A))),
% 0.35/0.59      inference('split', [status(esa)], ['3'])).
% 0.35/0.59  thf('38', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.35/0.59      inference('sat_resolution*', [status(thm)], ['2', '9', '37'])).
% 0.35/0.59  thf('39', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.35/0.59      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.35/0.59  thf('40', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.35/0.59      inference('sup-', [status(thm)], ['35', '39'])).
% 0.35/0.59  thf('41', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.35/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.35/0.59  thf('42', plain, ($false), inference('demod', [status(thm)], ['11', '41'])).
% 0.35/0.59  
% 0.35/0.59  % SZS output end Refutation
% 0.35/0.59  
% 0.35/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
