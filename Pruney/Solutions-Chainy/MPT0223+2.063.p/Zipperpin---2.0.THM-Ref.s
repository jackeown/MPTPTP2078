%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.28mptY7Iln

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:38 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   74 (  83 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  516 ( 603 expanded)
%              Number of equality atoms :   58 (  71 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','8'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k2_tarski @ X21 @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X27 @ X26 @ X25 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['13','32'])).

thf('34',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.28mptY7Iln
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:59:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 481 iterations in 0.191s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.63  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(d1_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.64       ( ![E:$i]:
% 0.45/0.64         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.64           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, axiom,
% 0.45/0.64    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.64       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.45/0.64          | ((X10) = (X11))
% 0.45/0.64          | ((X10) = (X12))
% 0.45/0.64          | ((X10) = (X13)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t18_zfmisc_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.64         ( k1_tarski @ A ) ) =>
% 0.45/0.64       ( ( A ) = ( B ) ) ))).
% 0.45/0.64  thf(zf_stmt_1, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i]:
% 0.45/0.64        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.64            ( k1_tarski @ A ) ) =>
% 0.45/0.64          ( ( A ) = ( B ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.45/0.64         = (k1_tarski @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.64  thf(t100_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.64           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.45/0.64         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf(t21_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.64           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.45/0.64           = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf(t46_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.45/0.64  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['3', '8'])).
% 0.45/0.64  thf(t98_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X7 @ X8)
% 0.45/0.64           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.45/0.64         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.64  thf(t5_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.64  thf('12', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.45/0.64         = (k1_tarski @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf(t69_enumset1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.64  thf(l53_enumset1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.45/0.64       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.64         ((k2_enumset1 @ X21 @ X22 @ X23 @ X24)
% 0.45/0.64           = (k2_xboole_0 @ (k2_tarski @ X21 @ X22) @ (k2_tarski @ X23 @ X24)))),
% 0.45/0.64      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.45/0.64           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf(t71_enumset1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.64         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.45/0.64           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.45/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.64  thf(t102_enumset1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.64         ((k1_enumset1 @ X27 @ X26 @ X25) = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.45/0.64      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.45/0.64  thf(t70_enumset1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X29 : $i, X30 : $i]:
% 0.45/0.64         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['18', '21'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X29 : $i, X30 : $i]:
% 0.45/0.64         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.64  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_3, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.64       ( ![E:$i]:
% 0.45/0.64         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.45/0.64          | (r2_hidden @ X14 @ X18)
% 0.45/0.64          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.64         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.45/0.64          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.45/0.64      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.64          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['23', '25'])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.64         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.45/0.64      inference('simplify', [status(thm)], ['27'])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['26', '28'])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (r2_hidden @ X0 @ (k2_enumset1 @ X1 @ X1 @ X0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['22', '29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (r2_hidden @ X0 @ 
% 0.45/0.64          (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['14', '31'])).
% 0.45/0.64  thf('33', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['13', '32'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X29 : $i, X30 : $i]:
% 0.45/0.64         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X19 @ X18)
% 0.45/0.64          | ~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.45/0.64          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.45/0.64         (~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.45/0.64          | ~ (r2_hidden @ X19 @ (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['36'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.64          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['35', '37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.45/0.64          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['34', '38'])).
% 0.45/0.64  thf('40', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.45/0.64      inference('sup-', [status(thm)], ['33', '39'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['0', '40'])).
% 0.45/0.64  thf('42', plain, (((sk_A) = (sk_B))),
% 0.45/0.64      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.64  thf('43', plain, (((sk_A) != (sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.64  thf('44', plain, ($false),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
