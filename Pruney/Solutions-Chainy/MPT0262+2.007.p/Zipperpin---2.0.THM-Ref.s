%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nsnSrPRDuI

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  357 ( 466 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t57_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ B )
          & ~ ( r2_hidden @ C @ B )
          & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t57_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf(t114_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ D )
        & ( r1_xboole_0 @ B @ D )
        & ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X1 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t114_xboole_1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X1 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X3 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ ( k1_tarski @ X1 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ X3 @ ( k1_tarski @ X2 ) ) ) @ X0 )
      | ~ ( r1_xboole_0 @ X3 @ X0 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X2 ) ) ) @ X0 )
      | ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_tarski @ X1 @ X2 ) ) @ X0 )
      | ( r2_hidden @ X3 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X3 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nsnSrPRDuI
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 122 iterations in 0.055s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(t57_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.20/0.51          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.20/0.51             ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t57_zfmisc_1])).
% 0.20/0.51  thf('0', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t56_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k1_tarski @ X14) @ X15) | (r2_hidden @ X14 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t56_zfmisc_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k1_tarski @ X14) @ X15) | (r2_hidden @ X14 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t56_zfmisc_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k1_tarski @ X14) @ X15) | (r2_hidden @ X14 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t56_zfmisc_1])).
% 0.20/0.51  thf(t114_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 0.20/0.51         ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.51       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ X2 @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t114_xboole_1])).
% 0.20/0.51  thf(t4_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.51       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.51           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)) @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ X2 @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0)
% 0.20/0.51          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.20/0.51          | ~ (r1_xboole_0 @ X3 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ 
% 0.20/0.51             (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ (k1_tarski @ X1))) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ 
% 0.20/0.51             (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.51              (k2_xboole_0 @ X3 @ (k1_tarski @ X2))) @ 
% 0.20/0.51             X0)
% 0.20/0.51          | ~ (r1_xboole_0 @ X3 @ X0)
% 0.20/0.51          | (r2_hidden @ X2 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0)
% 0.20/0.51          | (r2_hidden @ X2 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ 
% 0.20/0.51             (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.20/0.51              (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X2))) @ 
% 0.20/0.51             X0)
% 0.20/0.51          | (r2_hidden @ X3 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.51  thf(t41_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k2_tarski @ A @ B ) =
% 0.20/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((k2_tarski @ X12 @ X13)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0)
% 0.20/0.51          | (r2_hidden @ X2 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ 
% 0.20/0.51             (k2_xboole_0 @ (k1_tarski @ X3) @ (k2_tarski @ X1 @ X2)) @ X0)
% 0.20/0.51          | (r2_hidden @ X3 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((k2_tarski @ X12 @ X13)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((k2_tarski @ X12 @ X13)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.51           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.51  thf(t7_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (r1_tarski @ (k2_xboole_0 @ X2 @ X1) @ 
% 0.20/0.51          (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (r1_tarski @ (k2_xboole_0 @ X2 @ (k1_tarski @ X1)) @ 
% 0.20/0.51          (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['13', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (r1_tarski @ (k2_tarski @ X1 @ X0) @ 
% 0.20/0.51          (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X2)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['12', '17'])).
% 0.20/0.51  thf(t63_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.51       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X7 @ X8)
% 0.20/0.51          | ~ (r1_xboole_0 @ X8 @ X9)
% 0.20/0.51          | (r1_xboole_0 @ X7 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k2_tarski @ X2 @ X1) @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ 
% 0.20/0.51               (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)) @ X3))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((r2_hidden @ X3 @ X0)
% 0.20/0.51          | (r2_hidden @ X1 @ X0)
% 0.20/0.51          | (r2_hidden @ X2 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ (k2_tarski @ X3 @ X2) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '20'])).
% 0.20/0.51  thf('22', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ sk_B)
% 0.20/0.51          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.51          | (r2_hidden @ X1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain, (~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain, (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_C @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
