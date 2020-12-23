%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K78iH5ognq

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:49 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 100 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  564 ( 675 expanded)
%              Number of equality atoms :   58 (  73 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['7','20','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X30 @ X31 @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X17 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K78iH5ognq
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 1007 iterations in 0.478s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.96  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.75/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.96  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.96  thf(d1_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.96           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, axiom,
% 0.75/0.96    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.96     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.96       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.96  thf('0', plain,
% 0.75/0.96      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.75/0.96          | ((X16) = (X17))
% 0.75/0.96          | ((X16) = (X18))
% 0.75/0.96          | ((X16) = (X19)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(t6_zfmisc_1, conjecture,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.75/0.96       ( ( A ) = ( B ) ) ))).
% 0.75/0.96  thf(zf_stmt_1, negated_conjecture,
% 0.75/0.96    (~( ![A:$i,B:$i]:
% 0.75/0.96        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.75/0.96          ( ( A ) = ( B ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.75/0.96  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.96  thf(t28_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.96  thf('2', plain,
% 0.75/0.96      (![X4 : $i, X5 : $i]:
% 0.75/0.96         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.75/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.96  thf('3', plain,
% 0.75/0.96      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.75/0.96         = (k1_tarski @ sk_A))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.96  thf(t100_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      (![X2 : $i, X3 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X2 @ X3)
% 0.75/0.96           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.75/0.96         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['3', '4'])).
% 0.75/0.96  thf(t98_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.75/0.96  thf('6', plain,
% 0.75/0.96      (![X13 : $i, X14 : $i]:
% 0.75/0.96         ((k2_xboole_0 @ X13 @ X14)
% 0.75/0.96           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.96  thf('7', plain,
% 0.75/0.96      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.75/0.96         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.75/0.96            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.75/0.96      inference('sup+', [status(thm)], ['5', '6'])).
% 0.75/0.96  thf(idempotence_k3_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.75/0.96  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.96      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.75/0.96  thf('9', plain,
% 0.75/0.96      (![X2 : $i, X3 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X2 @ X3)
% 0.75/0.96           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.96  thf('10', plain,
% 0.75/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['8', '9'])).
% 0.75/0.96  thf(t79_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.75/0.96  thf('11', plain,
% 0.75/0.96      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.75/0.96      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.75/0.96  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.75/0.96      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.96  thf(t69_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.96       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.75/0.96  thf('13', plain,
% 0.75/0.96      (![X9 : $i, X10 : $i]:
% 0.75/0.96         (~ (r1_xboole_0 @ X9 @ X10)
% 0.75/0.96          | ~ (r1_tarski @ X9 @ X10)
% 0.75/0.96          | (v1_xboole_0 @ X9))),
% 0.75/0.96      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.75/0.96  thf('14', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 0.75/0.96          | ~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.96  thf('15', plain,
% 0.75/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['8', '9'])).
% 0.75/0.96  thf(t36_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.75/0.96  thf('16', plain,
% 0.75/0.96      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.75/0.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.75/0.96  thf('17', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.75/0.96      inference('sup+', [status(thm)], ['15', '16'])).
% 0.75/0.96  thf('18', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['14', '17'])).
% 0.75/0.96  thf(l13_xboole_0, axiom,
% 0.75/0.96    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.96  thf('19', plain,
% 0.75/0.96      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.75/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.75/0.96  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.96  thf(t5_boole, axiom,
% 0.75/0.96    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.96  thf('21', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.75/0.96      inference('cnf', [status(esa)], [t5_boole])).
% 0.75/0.96  thf('22', plain,
% 0.75/0.96      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.75/0.96         = (k1_tarski @ sk_B))),
% 0.75/0.96      inference('demod', [status(thm)], ['7', '20', '21'])).
% 0.75/0.96  thf(t69_enumset1, axiom,
% 0.75/0.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.96  thf('23', plain,
% 0.75/0.96      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.75/0.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.96  thf(t70_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.96  thf('24', plain,
% 0.75/0.96      (![X35 : $i, X36 : $i]:
% 0.75/0.96         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.96  thf(t46_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.75/0.96       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.75/0.96  thf('25', plain,
% 0.75/0.96      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.96         ((k2_enumset1 @ X30 @ X31 @ X32 @ X33)
% 0.75/0.96           = (k2_xboole_0 @ (k1_enumset1 @ X30 @ X31 @ X32) @ (k1_tarski @ X33)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.75/0.96  thf('26', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.75/0.96           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['24', '25'])).
% 0.75/0.96  thf('27', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.75/0.96           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['23', '26'])).
% 0.75/0.96  thf(t71_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.75/0.96  thf('28', plain,
% 0.75/0.96      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.75/0.96         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.75/0.96           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.75/0.96      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.75/0.96  thf('29', plain,
% 0.75/0.96      (![X35 : $i, X36 : $i]:
% 0.75/0.96         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.96  thf('30', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['28', '29'])).
% 0.75/0.96  thf('31', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((k2_tarski @ X0 @ X1)
% 0.75/0.96           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.75/0.96      inference('demod', [status(thm)], ['27', '30'])).
% 0.75/0.96  thf('32', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.75/0.96      inference('demod', [status(thm)], ['22', '31'])).
% 0.75/0.96  thf('33', plain,
% 0.75/0.96      (![X35 : $i, X36 : $i]:
% 0.75/0.96         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.96  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.96  thf(zf_stmt_3, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.96  thf('34', plain,
% 0.75/0.96      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.75/0.96          | (r2_hidden @ X20 @ X24)
% 0.75/0.96          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.96  thf('35', plain,
% 0.75/0.96      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.96         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.75/0.96          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.75/0.96      inference('simplify', [status(thm)], ['34'])).
% 0.75/0.96  thf('36', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.96          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['33', '35'])).
% 0.75/0.96  thf('37', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.75/0.96         (((X16) != (X17)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('38', plain,
% 0.75/0.96      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.75/0.96         ~ (zip_tseitin_0 @ X17 @ X17 @ X18 @ X15)),
% 0.75/0.96      inference('simplify', [status(thm)], ['37'])).
% 0.75/0.96  thf('39', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['36', '38'])).
% 0.75/0.96  thf('40', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.75/0.96      inference('sup+', [status(thm)], ['32', '39'])).
% 0.75/0.96  thf('41', plain,
% 0.75/0.96      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.75/0.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.96  thf('42', plain,
% 0.75/0.96      (![X35 : $i, X36 : $i]:
% 0.75/0.96         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.96  thf('43', plain,
% 0.75/0.96      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X25 @ X24)
% 0.75/0.96          | ~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.75/0.96          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.96  thf('44', plain,
% 0.75/0.96      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.75/0.96         (~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.75/0.96          | ~ (r2_hidden @ X25 @ (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['43'])).
% 0.75/0.96  thf('45', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.96          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['42', '44'])).
% 0.75/0.96  thf('46', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.96          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['41', '45'])).
% 0.75/0.96  thf('47', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.75/0.96      inference('sup-', [status(thm)], ['40', '46'])).
% 0.75/0.96  thf('48', plain,
% 0.75/0.96      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['0', '47'])).
% 0.75/0.96  thf('49', plain, (((sk_A) = (sk_B))),
% 0.75/0.96      inference('simplify', [status(thm)], ['48'])).
% 0.75/0.96  thf('50', plain, (((sk_A) != (sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.96  thf('51', plain, ($false),
% 0.75/0.96      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.75/0.96  
% 0.75/0.96  % SZS output end Refutation
% 0.75/0.96  
% 0.75/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
