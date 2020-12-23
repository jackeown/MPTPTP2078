%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qbNdTKFWMM

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:37 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   74 (  82 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  488 ( 554 expanded)
%              Number of equality atoms :   63 (  73 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','15'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('27',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
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

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X11 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('39',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qbNdTKFWMM
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:07:33 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 290 iterations in 0.132s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(t18_zfmisc_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.59         ( k1_tarski @ A ) ) =>
% 0.40/0.59       ( ( A ) = ( B ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i]:
% 0.40/0.59        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.59            ( k1_tarski @ A ) ) =>
% 0.40/0.59          ( ( A ) = ( B ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.40/0.59         = (k1_tarski @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t100_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X1 @ X2)
% 0.40/0.59           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.40/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.59  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X1 @ X2)
% 0.40/0.59           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.40/0.59  thf(t2_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X1 : $i, X2 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X1 @ X2)
% 0.40/0.59           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf(t5_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.59  thf('9', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.59  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf(t48_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X4 : $i, X5 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.40/0.59           = (k3_xboole_0 @ X4 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.59  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.59  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['5', '14'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '15'])).
% 0.40/0.59  thf(t98_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i]:
% 0.40/0.59         ((k2_xboole_0 @ X7 @ X8)
% 0.40/0.59           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('19', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.59         = (k1_tarski @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf(t69_enumset1, axiom,
% 0.40/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.40/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.59  thf(t70_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X34 : $i, X35 : $i]:
% 0.40/0.59         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.40/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.59  thf(t46_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.40/0.59       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X29 @ X30 @ X31 @ X32)
% 0.40/0.59           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ (k1_tarski @ X32)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.40/0.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.40/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['21', '24'])).
% 0.40/0.59  thf(t71_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.40/0.59           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.40/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X34 : $i, X35 : $i]:
% 0.40/0.59         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.40/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_tarski @ X0 @ X1)
% 0.40/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.40/0.59      inference('demod', [status(thm)], ['25', '28'])).
% 0.40/0.59  thf('30', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['20', '29'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X34 : $i, X35 : $i]:
% 0.40/0.59         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.40/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.59  thf(d1_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.59       ( ![E:$i]:
% 0.40/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_2, axiom,
% 0.40/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_3, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.59       ( ![E:$i]:
% 0.40/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.40/0.59          | (r2_hidden @ X14 @ X18)
% 0.40/0.59          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.59         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.40/0.59          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.40/0.59      inference('simplify', [status(thm)], ['32'])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.59      inference('sup+', [status(thm)], ['31', '33'])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.59         (((X10) != (X11)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X11 @ X11 @ X12 @ X9)),
% 0.40/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['34', '36'])).
% 0.40/0.59  thf('38', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['30', '37'])).
% 0.40/0.59  thf(d1_tarski, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X24 @ X23)
% 0.40/0.59          | ((X24) = (X21))
% 0.40/0.59          | ((X23) != (k1_tarski @ X21)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X21 : $i, X24 : $i]:
% 0.40/0.59         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.40/0.59  thf('41', plain, (((sk_A) = (sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['38', '40'])).
% 0.40/0.59  thf('42', plain, (((sk_A) != (sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('43', plain, ($false),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
