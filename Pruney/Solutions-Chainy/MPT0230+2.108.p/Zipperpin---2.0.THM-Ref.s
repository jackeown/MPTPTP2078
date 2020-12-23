%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OiRPQXZ6mD

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:23 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   80 (  91 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  557 ( 669 expanded)
%              Number of equality atoms :   67 (  84 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','19','20'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X34 @ X35 @ X36 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X41 @ X41 @ X42 @ X43 )
      = ( k1_enumset1 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('27',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k1_enumset1 @ X66 @ X68 @ X67 )
      = ( k1_enumset1 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X33 @ X32 @ X31 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['21','26','29'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OiRPQXZ6mD
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:58:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 506 iterations in 0.163s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(d1_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.61       ( ![E:$i]:
% 0.37/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.37/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, axiom,
% 0.37/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.37/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.37/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.61         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.37/0.61          | ((X12) = (X13))
% 0.37/0.61          | ((X12) = (X14))
% 0.37/0.61          | ((X12) = (X15)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t25_zfmisc_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.37/0.61          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.61        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.37/0.61             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.61  thf(t28_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X3 : $i, X4 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.37/0.61         = (k1_tarski @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf(t100_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X1 : $i, X2 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.37/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.61  thf(t98_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X9 @ X10)
% 0.37/0.61           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.37/0.61         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ 
% 0.37/0.61            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.37/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf(t2_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X1 : $i, X2 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.61  thf(t5_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.61  thf('11', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.61  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.61  thf(t48_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.37/0.61           = (k3_xboole_0 @ X6 @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.61  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X1 : $i, X2 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.61           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.61  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.37/0.61  thf('20', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.37/0.61         = (k2_tarski @ sk_B @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['7', '19', '20'])).
% 0.37/0.61  thf(t70_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X39 : $i, X40 : $i]:
% 0.37/0.61         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 0.37/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.61  thf(t46_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.37/0.61       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.61         ((k2_enumset1 @ X34 @ X35 @ X36 @ X37)
% 0.37/0.61           = (k2_xboole_0 @ (k1_enumset1 @ X34 @ X35 @ X36) @ (k1_tarski @ X37)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.37/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.61  thf(t71_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.37/0.61         ((k2_enumset1 @ X41 @ X41 @ X42 @ X43)
% 0.37/0.61           = (k1_enumset1 @ X41 @ X42 @ X43))),
% 0.37/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.37/0.61           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.61  thf(t98_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.37/0.61         ((k1_enumset1 @ X66 @ X68 @ X67) = (k1_enumset1 @ X66 @ X67 @ X68))),
% 0.37/0.61      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.37/0.61  thf(t102_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.61         ((k1_enumset1 @ X33 @ X32 @ X31) = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.37/0.61      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['21', '26', '29'])).
% 0.37/0.61  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.37/0.61  thf(zf_stmt_3, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.61       ( ![E:$i]:
% 0.37/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.61         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.37/0.61          | (r2_hidden @ X16 @ X20)
% 0.37/0.61          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.61         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.37/0.61          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.37/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.37/0.61          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['30', '32'])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.61         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.37/0.61         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X11)),
% 0.37/0.61      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.61  thf('36', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['33', '35'])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X39 : $i, X40 : $i]:
% 0.37/0.61         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 0.37/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X21 @ X20)
% 0.37/0.61          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.37/0.61          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.37/0.61         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.37/0.61          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['37', '39'])).
% 0.37/0.61  thf('41', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.37/0.61      inference('sup-', [status(thm)], ['36', '40'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '41'])).
% 0.37/0.61  thf('43', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.61  thf('44', plain, (((sk_A) != (sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.61  thf('45', plain, (((sk_A) != (sk_C))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.61  thf('46', plain, ($false),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['43', '44', '45'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
