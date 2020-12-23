%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ql5ZSVtGBL

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:38 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   75 (  93 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  538 ( 709 expanded)
%              Number of equality atoms :   59 (  82 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_tarski @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k1_tarski @ X28 ) @ ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('7',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('10',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['7','24','25'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
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

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X15 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ql5ZSVtGBL
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.51/1.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.76  % Solved by: fo/fo7.sh
% 1.51/1.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.76  % done 325 iterations in 1.311s
% 1.51/1.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.76  % SZS output start Refutation
% 1.51/1.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.51/1.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.51/1.76  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.51/1.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.51/1.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.51/1.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.51/1.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.51/1.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.76  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.51/1.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.51/1.76  thf(d1_enumset1, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.51/1.76       ( ![E:$i]:
% 1.51/1.76         ( ( r2_hidden @ E @ D ) <=>
% 1.51/1.76           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.51/1.76  thf(zf_stmt_0, axiom,
% 1.51/1.76    (![E:$i,C:$i,B:$i,A:$i]:
% 1.51/1.76     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.51/1.76       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.51/1.76  thf('0', plain,
% 1.51/1.76      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 1.51/1.76          | ((X14) = (X15))
% 1.51/1.76          | ((X14) = (X16))
% 1.51/1.76          | ((X14) = (X17)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf(t18_zfmisc_1, conjecture,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.51/1.76         ( k1_tarski @ A ) ) =>
% 1.51/1.76       ( ( A ) = ( B ) ) ))).
% 1.51/1.76  thf(zf_stmt_1, negated_conjecture,
% 1.51/1.76    (~( ![A:$i,B:$i]:
% 1.51/1.76        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.51/1.76            ( k1_tarski @ A ) ) =>
% 1.51/1.76          ( ( A ) = ( B ) ) ) )),
% 1.51/1.76    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 1.51/1.76  thf('1', plain,
% 1.51/1.76      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.51/1.76         = (k1_tarski @ sk_A))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf(t100_xboole_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.51/1.76  thf('2', plain,
% 1.51/1.76      (![X6 : $i, X7 : $i]:
% 1.51/1.76         ((k4_xboole_0 @ X6 @ X7)
% 1.51/1.76           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.51/1.76  thf('3', plain,
% 1.51/1.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.51/1.76         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['1', '2'])).
% 1.51/1.76  thf(t98_xboole_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.51/1.76  thf('4', plain,
% 1.51/1.76      (![X11 : $i, X12 : $i]:
% 1.51/1.76         ((k2_xboole_0 @ X11 @ X12)
% 1.51/1.76           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.51/1.76  thf('5', plain,
% 1.51/1.76      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.51/1.76         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 1.51/1.76            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 1.51/1.76      inference('sup+', [status(thm)], ['3', '4'])).
% 1.51/1.76  thf(t41_enumset1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( k2_tarski @ A @ B ) =
% 1.51/1.76       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 1.51/1.76  thf('6', plain,
% 1.51/1.76      (![X28 : $i, X29 : $i]:
% 1.51/1.76         ((k2_tarski @ X28 @ X29)
% 1.51/1.76           = (k2_xboole_0 @ (k1_tarski @ X28) @ (k1_tarski @ X29)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.51/1.76  thf('7', plain,
% 1.51/1.76      (((k2_tarski @ sk_B @ sk_A)
% 1.51/1.76         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 1.51/1.76            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 1.51/1.76      inference('demod', [status(thm)], ['5', '6'])).
% 1.51/1.76  thf('8', plain,
% 1.51/1.76      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.51/1.76         = (k1_tarski @ sk_A))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf(l97_xboole_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.51/1.76  thf('9', plain,
% 1.51/1.76      (![X4 : $i, X5 : $i]:
% 1.51/1.76         (r1_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ (k5_xboole_0 @ X4 @ X5))),
% 1.51/1.76      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.51/1.76  thf('10', plain,
% 1.51/1.76      ((r1_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.51/1.76        (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 1.51/1.76      inference('sup+', [status(thm)], ['8', '9'])).
% 1.51/1.76  thf(d7_xboole_0, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.51/1.76       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.51/1.76  thf('11', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]:
% 1.51/1.76         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.51/1.76      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.51/1.76  thf('12', plain,
% 1.51/1.76      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.51/1.76         (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 1.51/1.76         = (k1_xboole_0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['10', '11'])).
% 1.51/1.76  thf('13', plain,
% 1.51/1.76      (![X6 : $i, X7 : $i]:
% 1.51/1.76         ((k4_xboole_0 @ X6 @ X7)
% 1.51/1.76           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.51/1.76  thf('14', plain,
% 1.51/1.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.51/1.76         (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 1.51/1.76         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 1.51/1.76      inference('sup+', [status(thm)], ['12', '13'])).
% 1.51/1.76  thf(t5_boole, axiom,
% 1.51/1.76    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.51/1.76  thf('15', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.51/1.76      inference('cnf', [status(esa)], [t5_boole])).
% 1.51/1.76  thf('16', plain,
% 1.51/1.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.51/1.76         (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 1.51/1.76         = (k1_tarski @ sk_A))),
% 1.51/1.76      inference('demod', [status(thm)], ['14', '15'])).
% 1.51/1.76  thf(t48_xboole_1, axiom,
% 1.51/1.76    (![A:$i,B:$i]:
% 1.51/1.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.51/1.76  thf('17', plain,
% 1.51/1.76      (![X8 : $i, X9 : $i]:
% 1.51/1.76         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.51/1.76           = (k3_xboole_0 @ X8 @ X9))),
% 1.51/1.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.51/1.76  thf('18', plain,
% 1.51/1.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 1.51/1.76         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.51/1.76            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 1.51/1.76      inference('sup+', [status(thm)], ['16', '17'])).
% 1.51/1.76  thf(idempotence_k3_xboole_0, axiom,
% 1.51/1.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.51/1.76  thf('19', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.51/1.76      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.51/1.76  thf('20', plain,
% 1.51/1.76      (![X6 : $i, X7 : $i]:
% 1.51/1.76         ((k4_xboole_0 @ X6 @ X7)
% 1.51/1.76           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.51/1.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.51/1.76  thf('21', plain,
% 1.51/1.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.76      inference('sup+', [status(thm)], ['19', '20'])).
% 1.51/1.76  thf('22', plain,
% 1.51/1.76      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 1.51/1.76         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.51/1.76            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 1.51/1.76      inference('demod', [status(thm)], ['18', '21'])).
% 1.51/1.76  thf('23', plain,
% 1.51/1.76      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.51/1.76         (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 1.51/1.76         = (k1_xboole_0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['10', '11'])).
% 1.51/1.76  thf('24', plain,
% 1.51/1.76      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 1.51/1.76      inference('sup+', [status(thm)], ['22', '23'])).
% 1.51/1.76  thf('25', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.51/1.76      inference('cnf', [status(esa)], [t5_boole])).
% 1.51/1.76  thf('26', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 1.51/1.76      inference('demod', [status(thm)], ['7', '24', '25'])).
% 1.51/1.76  thf(t70_enumset1, axiom,
% 1.51/1.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.51/1.76  thf('27', plain,
% 1.51/1.76      (![X31 : $i, X32 : $i]:
% 1.51/1.76         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 1.51/1.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.51/1.76  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.51/1.76  thf(zf_stmt_3, axiom,
% 1.51/1.76    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.51/1.76       ( ![E:$i]:
% 1.51/1.76         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.51/1.76  thf('28', plain,
% 1.51/1.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.51/1.76         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 1.51/1.76          | (r2_hidden @ X18 @ X22)
% 1.51/1.76          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.51/1.76  thf('29', plain,
% 1.51/1.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.51/1.76         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 1.51/1.76          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 1.51/1.76      inference('simplify', [status(thm)], ['28'])).
% 1.51/1.76  thf('30', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.51/1.76          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.51/1.76      inference('sup+', [status(thm)], ['27', '29'])).
% 1.51/1.76  thf('31', plain,
% 1.51/1.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.51/1.76         (((X14) != (X15)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.76  thf('32', plain,
% 1.51/1.76      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.51/1.76         ~ (zip_tseitin_0 @ X15 @ X15 @ X16 @ X13)),
% 1.51/1.76      inference('simplify', [status(thm)], ['31'])).
% 1.51/1.76  thf('33', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.51/1.76      inference('sup-', [status(thm)], ['30', '32'])).
% 1.51/1.76  thf('34', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 1.51/1.76      inference('sup+', [status(thm)], ['26', '33'])).
% 1.51/1.76  thf(t69_enumset1, axiom,
% 1.51/1.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.51/1.76  thf('35', plain,
% 1.51/1.76      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 1.51/1.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.51/1.76  thf('36', plain,
% 1.51/1.76      (![X31 : $i, X32 : $i]:
% 1.51/1.76         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 1.51/1.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.51/1.76  thf('37', plain,
% 1.51/1.76      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.51/1.76         (~ (r2_hidden @ X23 @ X22)
% 1.51/1.76          | ~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 1.51/1.76          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.51/1.76  thf('38', plain,
% 1.51/1.76      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.51/1.76         (~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 1.51/1.76          | ~ (r2_hidden @ X23 @ (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.51/1.76      inference('simplify', [status(thm)], ['37'])).
% 1.51/1.76  thf('39', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.76         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.51/1.76          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.51/1.76      inference('sup-', [status(thm)], ['36', '38'])).
% 1.51/1.76  thf('40', plain,
% 1.51/1.76      (![X0 : $i, X1 : $i]:
% 1.51/1.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.51/1.76          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.51/1.76      inference('sup-', [status(thm)], ['35', '39'])).
% 1.51/1.76  thf('41', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 1.51/1.76      inference('sup-', [status(thm)], ['34', '40'])).
% 1.51/1.76  thf('42', plain,
% 1.51/1.76      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 1.51/1.76      inference('sup-', [status(thm)], ['0', '41'])).
% 1.51/1.76  thf('43', plain, (((sk_A) = (sk_B))),
% 1.51/1.76      inference('simplify', [status(thm)], ['42'])).
% 1.51/1.76  thf('44', plain, (((sk_A) != (sk_B))),
% 1.51/1.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.76  thf('45', plain, ($false),
% 1.51/1.76      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 1.51/1.76  
% 1.51/1.76  % SZS output end Refutation
% 1.51/1.76  
% 1.62/1.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
