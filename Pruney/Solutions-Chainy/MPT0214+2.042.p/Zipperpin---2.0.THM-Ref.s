%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ynlATWtbDD

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  83 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  430 ( 597 expanded)
%              Number of equality atoms :   47 (  65 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( X11 = X12 )
      | ( X11 = X13 )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('11',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X51
        = ( k1_tarski @ X50 ) )
      | ( X51 = k1_xboole_0 )
      | ~ ( r1_tarski @ X51 @ ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_A = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('26',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['26','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ynlATWtbDD
% 0.12/0.36  % Computer   : n010.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 20:19:14 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 194 iterations in 0.077s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(t69_enumset1, axiom,
% 0.22/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.55  thf('0', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.55  thf(t70_enumset1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i]:
% 0.22/0.55         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.22/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.55  thf(d1_enumset1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.55       ( ![E:$i]:
% 0.22/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.55  thf(zf_stmt_1, axiom,
% 0.22/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_2, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.55       ( ![E:$i]:
% 0.22/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.55         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.22/0.55          | (r2_hidden @ X15 @ X19)
% 0.22/0.55          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.55         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.22/0.55          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.22/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.55      inference('sup+', [status(thm)], ['1', '3'])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.55         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.22/0.55         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 0.22/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '6'])).
% 0.22/0.55  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['0', '7'])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.55         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.22/0.55          | ((X11) = (X12))
% 0.22/0.55          | ((X11) = (X13))
% 0.22/0.55          | ((X11) = (X14)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.55  thf(t6_zfmisc_1, conjecture,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.55       ( ( A ) = ( B ) ) ))).
% 0.22/0.55  thf(zf_stmt_3, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i]:
% 0.22/0.55        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.55          ( ( A ) = ( B ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.22/0.55  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.55  thf(l3_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X50 : $i, X51 : $i]:
% 0.22/0.55         (((X51) = (k1_tarski @ X50))
% 0.22/0.55          | ((X51) = (k1_xboole_0))
% 0.22/0.55          | ~ (r1_tarski @ X51 @ (k1_tarski @ X50)))),
% 0.22/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.55        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i]:
% 0.22/0.55         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.22/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X20 @ X19)
% 0.22/0.55          | ~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.22/0.55          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.22/0.55         (~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.22/0.55          | ~ (r2_hidden @ X20 @ (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.55          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.55          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.55          | ~ (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '18'])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((X0) = (sk_B))
% 0.22/0.55          | ((X0) = (sk_B))
% 0.22/0.55          | ((X0) = (sk_B))
% 0.22/0.55          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['9', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.55          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.55          | ((X0) = (sk_B)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      ((((sk_A) = (sk_B)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '21'])).
% 0.22/0.55  thf('23', plain, (((sk_A) != (sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.55  thf('24', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('25', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['0', '7'])).
% 0.22/0.55  thf('26', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.22/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf(t3_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.55  thf('27', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.55  thf('28', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf(t28_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i]:
% 0.22/0.55         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.55  thf(t100_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.22/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.55           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.55  thf(t1_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.22/0.55       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.55          | ~ (r2_hidden @ X0 @ X2)
% 0.22/0.55          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.22/0.55          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.22/0.55          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.22/0.55          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['27', '35'])).
% 0.22/0.55  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.55  thf('38', plain, ($false), inference('sup-', [status(thm)], ['26', '37'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
