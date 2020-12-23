%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pcMg8MSued

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:47 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 310 expanded)
%              Number of leaves         :   28 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  536 (2463 expanded)
%              Number of equality atoms :   76 ( 326 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_tarski @ X19 @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('6',plain,(
    ! [X34: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X32 @ X33 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X32 ) @ ( k1_setfam_1 @ X33 ) ) )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X34: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X34: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('30',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('32',plain,(
    ! [X34: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('33',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('37',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['24','27'])).

thf('41',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['28','29'])).

thf('42',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['30','37'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','38','39','40','41','42','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pcMg8MSued
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 202 iterations in 0.122s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(t12_setfam_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i]:
% 0.39/0.58        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.58         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t69_enumset1, axiom,
% 0.39/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.58  thf('1', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.58  thf(t43_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.39/0.58       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X19 @ X20 @ X21)
% 0.39/0.58           = (k2_xboole_0 @ (k2_tarski @ X19 @ X20) @ (k1_tarski @ X21)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.39/0.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf(t70_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X23 : $i, X24 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.39/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k2_tarski @ X0 @ X1)
% 0.39/0.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.39/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf(t11_setfam_1, axiom,
% 0.39/0.58    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.39/0.58  thf('6', plain, (![X34 : $i]: ((k1_setfam_1 @ (k1_tarski @ X34)) = (X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.39/0.58  thf(t10_setfam_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.58          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.39/0.58            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X32 : $i, X33 : $i]:
% 0.39/0.58         (((X32) = (k1_xboole_0))
% 0.39/0.58          | ((k1_setfam_1 @ (k2_xboole_0 @ X32 @ X33))
% 0.39/0.58              = (k3_xboole_0 @ (k1_setfam_1 @ X32) @ (k1_setfam_1 @ X33)))
% 0.39/0.58          | ((X33) = (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.39/0.58            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.39/0.58          | ((X1) = (k1_xboole_0))
% 0.39/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.39/0.58            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.39/0.58          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.39/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['5', '8'])).
% 0.39/0.58  thf('10', plain, (![X34 : $i]: ((k1_setfam_1 @ (k1_tarski @ X34)) = (X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.39/0.58          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.39/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.58         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.39/0.58        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.39/0.58        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.39/0.58        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X23 : $i, X24 : $i]:
% 0.39/0.58         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.39/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.58  thf(d1_enumset1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.58       ( ![E:$i]:
% 0.39/0.58         ( ( r2_hidden @ E @ D ) <=>
% 0.39/0.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_2, axiom,
% 0.39/0.58    (![E:$i,C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.39/0.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_3, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.58       ( ![E:$i]:
% 0.39/0.58         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.58         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.39/0.58          | (r2_hidden @ X12 @ X16)
% 0.39/0.58          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 0.39/0.58          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 0.39/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.39/0.58          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.39/0.58      inference('sup+', [status(thm)], ['16', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.58         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X7)),
% 0.39/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '21'])).
% 0.39/0.58  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['15', '22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (((r2_hidden @ sk_B @ k1_xboole_0) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['14', '23'])).
% 0.39/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.39/0.58  thf('25', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.58  thf(l24_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X28 : $i, X29 : $i]:
% 0.39/0.58         (~ (r1_xboole_0 @ (k1_tarski @ X28) @ X29) | ~ (r2_hidden @ X28 @ X29))),
% 0.39/0.58      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.39/0.58  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.58  thf('28', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.39/0.58      inference('clc', [status(thm)], ['24', '27'])).
% 0.39/0.58  thf('29', plain, (![X34 : $i]: ((k1_setfam_1 @ (k1_tarski @ X34)) = (X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.39/0.58  thf('30', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.39/0.58        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.39/0.58  thf('32', plain, (![X34 : $i]: ((k1_setfam_1 @ (k1_tarski @ X34)) = (X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.39/0.58        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['15', '22'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.39/0.58        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.58  thf('37', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.39/0.58      inference('clc', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('38', plain, (((sk_A) = (sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['30', '37'])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.58  thf('40', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.39/0.58      inference('clc', [status(thm)], ['24', '27'])).
% 0.39/0.58  thf('41', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf('42', plain, (((sk_A) = (sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['30', '37'])).
% 0.39/0.58  thf(t2_boole, axiom,
% 0.39/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.58  thf(t48_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X1 : $i, X2 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X2))
% 0.39/0.58           = (k3_xboole_0 @ X1 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (![X1 : $i, X2 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X2))
% 0.39/0.58           = (k3_xboole_0 @ X1 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.58           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['44', '45'])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.39/0.58           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['43', '46'])).
% 0.39/0.58  thf('48', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.58  thf(t83_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.58  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('52', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['47', '50', '51'])).
% 0.39/0.58  thf('53', plain, (((sk_A) != (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)],
% 0.39/0.58                ['0', '38', '39', '40', '41', '42', '52'])).
% 0.39/0.58  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
