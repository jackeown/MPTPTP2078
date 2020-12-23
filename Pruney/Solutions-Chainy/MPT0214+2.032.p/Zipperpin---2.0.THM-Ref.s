%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OO0Dp2YgVC

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  68 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  411 ( 443 expanded)
%              Number of equality atoms :   49 (  53 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X25 @ X26 @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X32 @ X32 @ X33 @ X34 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( X23 = X20 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OO0Dp2YgVC
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 98 iterations in 0.053s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(t6_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.47       ( ( A ) = ( B ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.47          ( ( A ) = ( B ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.47  thf('0', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t28_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.47         = (k1_tarski @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(t100_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.47           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.47         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(t92_xboole_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('5', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(t98_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ X6 @ X7)
% 0.21/0.47           = (k5_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.47         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf(t5_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.47  thf('9', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.47         = (k1_tarski @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(t69_enumset1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf(t70_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X30 : $i, X31 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.21/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.47  thf(t46_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.47       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X25 @ X26 @ X27 @ X28)
% 0.21/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X25 @ X26 @ X27) @ (k1_tarski @ X28)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.21/0.47           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['11', '14'])).
% 0.21/0.47  thf(t71_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X32 @ X32 @ X33 @ X34)
% 0.21/0.47           = (k1_enumset1 @ X32 @ X33 @ X34))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X30 : $i, X31 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.21/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k2_tarski @ X0 @ X1)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.47  thf('20', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X30 : $i, X31 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.21/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.47  thf(d1_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.47       ( ![E:$i]:
% 0.21/0.47         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_2, axiom,
% 0.21/0.47    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_3, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.47       ( ![E:$i]:
% 0.21/0.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.47         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.21/0.47          | (r2_hidden @ X13 @ X17)
% 0.21/0.47          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.47         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.21/0.47          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.21/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.47          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.47      inference('sup+', [status(thm)], ['21', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         (((X9) != (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X10 @ X10 @ X11 @ X8)),
% 0.21/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.47  thf('28', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.47      inference('sup+', [status(thm)], ['20', '27'])).
% 0.21/0.47  thf(d1_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X23 @ X22)
% 0.21/0.47          | ((X23) = (X20))
% 0.21/0.47          | ((X22) != (k1_tarski @ X20)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X20 : $i, X23 : $i]:
% 0.21/0.47         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.47  thf('31', plain, (((sk_A) = (sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.47  thf('32', plain, (((sk_A) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('33', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
