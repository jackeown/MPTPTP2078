%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2u4WnXdYMW

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:32 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   68 (  83 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  382 ( 515 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_A_1 @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A_1 @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A_1 @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('4',plain,
    ( ( sk_A_1
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_xboole_0 @ sk_A_1 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_xboole_0 @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X28 )
      | ( r2_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t58_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_xboole_0 @ X2 @ X0 )
      | ~ ( r2_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A_1
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_xboole_0 @ sk_A_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,
    ( ( r1_tarski @ sk_A_1 @ sk_B )
    | ( r2_xboole_0 @ sk_A_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('12',plain,(
    r1_tarski @ sk_A_1 @ sk_B ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_A_1 @ sk_B )
   <= ~ ( r1_tarski @ sk_A_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    r1_tarski @ sk_A_1 @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ sk_A_1 @ sk_C )
    | ~ ( r1_tarski @ sk_A_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ sk_A_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ sk_A_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X33: $i] :
      ( ( k5_xboole_0 @ X33 @ X33 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    ! [X33: $i] :
      ( ( k5_xboole_0 @ X33 @ X33 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ k1_xboole_0 )
      = X29 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ o_0_0_xboole_0 )
      = X29 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    r1_tarski @ sk_A_1 @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ( r1_xboole_0 @ X30 @ ( k4_xboole_0 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A_1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_A_1 @ sk_C ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['17','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2u4WnXdYMW
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 342 iterations in 0.256s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.73  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.54/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.54/0.73  thf(t106_xboole_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.54/0.73       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.73        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.54/0.73          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      ((~ (r1_tarski @ sk_A_1 @ sk_B) | ~ (r1_xboole_0 @ sk_A_1 @ sk_C))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      ((~ (r1_xboole_0 @ sk_A_1 @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A_1 @ sk_C)))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf('2', plain, ((r1_tarski @ sk_A_1 @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(d8_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.54/0.73       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X2 : $i, X4 : $i]:
% 0.54/0.73         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.54/0.73      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      ((((sk_A_1) = (k4_xboole_0 @ sk_B @ sk_C))
% 0.54/0.73        | (r2_xboole_0 @ sk_A_1 @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf(t36_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.54/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.73  thf(t58_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.54/0.73       ( r2_xboole_0 @ A @ C ) ))).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.73         (~ (r2_xboole_0 @ X26 @ X27)
% 0.54/0.73          | ~ (r1_tarski @ X27 @ X28)
% 0.54/0.73          | (r2_xboole_0 @ X26 @ X28))),
% 0.54/0.73      inference('cnf', [status(esa)], [t58_xboole_1])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((r2_xboole_0 @ X2 @ X0)
% 0.54/0.73          | ~ (r2_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      ((((sk_A_1) = (k4_xboole_0 @ sk_B @ sk_C))
% 0.54/0.73        | (r2_xboole_0 @ sk_A_1 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['4', '7'])).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.54/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (((r1_tarski @ sk_A_1 @ sk_B) | (r2_xboole_0 @ sk_A_1 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ~ (r2_xboole_0 @ X2 @ X3))),
% 0.54/0.73      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.54/0.73  thf('12', plain, ((r1_tarski @ sk_A_1 @ sk_B)),
% 0.54/0.73      inference('clc', [status(thm)], ['10', '11'])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      ((~ (r1_tarski @ sk_A_1 @ sk_B)) <= (~ ((r1_tarski @ sk_A_1 @ sk_B)))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf('14', plain, (((r1_tarski @ sk_A_1 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (~ ((r1_xboole_0 @ sk_A_1 @ sk_C)) | ~ ((r1_tarski @ sk_A_1 @ sk_B))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf('16', plain, (~ ((r1_xboole_0 @ sk_A_1 @ sk_C))),
% 0.54/0.73      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.54/0.73  thf('17', plain, (~ (r1_xboole_0 @ sk_A_1 @ sk_C)),
% 0.54/0.73      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.54/0.73  thf(t17_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.54/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.73  thf(t28_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (![X19 : $i, X20 : $i]:
% 0.54/0.73         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.54/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.54/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('demod', [status(thm)], ['20', '21'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf(t100_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X7 : $i, X8 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X7 @ X8)
% 0.54/0.73           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['23', '24'])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.54/0.73           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['22', '25'])).
% 0.54/0.73  thf(t49_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.54/0.73       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.54/0.73           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 0.54/0.73      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.54/0.73  thf(t92_xboole_1, axiom,
% 0.54/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.73  thf('28', plain, (![X33 : $i]: ((k5_xboole_0 @ X33 @ X33) = (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.73  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.54/0.73  thf('29', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      (![X33 : $i]: ((k5_xboole_0 @ X33 @ X33) = (o_0_0_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (o_0_0_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['26', '27', '30'])).
% 0.54/0.73  thf('32', plain,
% 0.54/0.73      (![X7 : $i, X8 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X7 @ X8)
% 0.54/0.73           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.54/0.73           = (k5_xboole_0 @ X0 @ o_0_0_xboole_0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['31', '32'])).
% 0.54/0.73  thf(t5_boole, axiom,
% 0.54/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.73  thf('34', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ k1_xboole_0) = (X29))),
% 0.54/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.73  thf('35', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (![X29 : $i]: ((k5_xboole_0 @ X29 @ o_0_0_xboole_0) = (X29))),
% 0.54/0.73      inference('demod', [status(thm)], ['34', '35'])).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.54/0.73      inference('demod', [status(thm)], ['33', '36'])).
% 0.54/0.73  thf('38', plain, ((r1_tarski @ sk_A_1 @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t85_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.54/0.73  thf('39', plain,
% 0.54/0.73      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.73         (~ (r1_tarski @ X30 @ X31)
% 0.54/0.73          | (r1_xboole_0 @ X30 @ (k4_xboole_0 @ X32 @ X31)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.54/0.73  thf('40', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (r1_xboole_0 @ sk_A_1 @ 
% 0.54/0.73          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.73  thf('41', plain, ((r1_xboole_0 @ sk_A_1 @ sk_C)),
% 0.54/0.73      inference('sup+', [status(thm)], ['37', '40'])).
% 0.54/0.73  thf('42', plain, ($false), inference('demod', [status(thm)], ['17', '41'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
