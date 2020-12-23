%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0qJWESslCZ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 288 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  400 (2144 expanded)
%              Number of equality atoms :   25 (  84 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('20',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_xboole_0 @ X2 @ X0 )
      | ~ ( r2_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( r2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('34',plain,
    ( ( sk_A = sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('36',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['17','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf('39',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('40',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_A
      = ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['34','35'])).

thf('43',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['34','35'])).

thf('44',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['37','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0qJWESslCZ
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:31:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 69 iterations in 0.037s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(t106_xboole_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.52       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.52          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf(t79_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.20/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t12_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.20/0.52         = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t70_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X12 @ X13)
% 0.20/0.52          | ~ (r1_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X15)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.20/0.52          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.52  thf('12', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('14', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('16', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.20/0.52  thf('18', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d8_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.52       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((((sk_A) = (k4_xboole_0 @ sk_B @ sk_C))
% 0.20/0.52        | (r2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf(t36_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.52  thf(t58_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.52       ( r2_xboole_0 @ A @ C ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_xboole_0 @ X9 @ X10)
% 0.20/0.52          | ~ (r1_tarski @ X10 @ X11)
% 0.20/0.52          | (r2_xboole_0 @ X9 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t58_xboole_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r2_xboole_0 @ X2 @ X0)
% 0.20/0.52          | ~ (r2_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((((sk_A) = (k4_xboole_0 @ sk_B @ sk_C)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((sk_A) = (k4_xboole_0 @ sk_B @ sk_C)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.20/0.52          | (r2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.20/0.52        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.20/0.52        | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['25', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((((sk_A) = (sk_B))
% 0.20/0.52        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.20/0.52        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['24', '30'])).
% 0.20/0.52  thf('32', plain, (((r2_xboole_0 @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('34', plain, ((((sk_A) = (sk_B)) | (r1_tarski @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.20/0.52  thf('36', plain, (((sk_A) = (sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain, (~ (r1_tarski @ sk_B @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((((sk_A) = (k4_xboole_0 @ sk_B @ sk_C))
% 0.20/0.52        | (r2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.20/0.52        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.20/0.52        | ((sk_A) = (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((((sk_A) = (k4_xboole_0 @ sk_B @ sk_C)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.52  thf('42', plain, (((sk_A) = (sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('43', plain, (((sk_A) = (sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      ((((sk_B) = (k4_xboole_0 @ sk_B @ sk_C)) | (r2_xboole_0 @ sk_B @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('46', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.52  thf('47', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.52      inference('clc', [status(thm)], ['44', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.52  thf('49', plain, ((r1_tarski @ sk_B @ sk_B)),
% 0.20/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain, ($false), inference('demod', [status(thm)], ['37', '49'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
