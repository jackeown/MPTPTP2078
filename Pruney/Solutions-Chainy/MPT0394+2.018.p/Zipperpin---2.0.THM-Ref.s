%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ap5xSgPDV9

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 533 expanded)
%              Number of leaves         :   27 ( 175 expanded)
%              Depth                    :   15
%              Number of atoms          :  586 (4688 expanded)
%              Number of equality atoms :   83 ( 645 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('14',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X30 ) @ ( k1_setfam_1 @ X31 ) ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('27',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
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

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('39',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('42',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('43',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference(clc,[status(thm)],['46','49'])).

thf('51',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['25','36'])).

thf('54',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['37','38'])).

thf('55',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['39','50'])).

thf('56',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('57',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','51','52','53','54','55','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ap5xSgPDV9
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 210 iterations in 0.127s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(t12_setfam_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.55         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.55  thf('1', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.55  thf(d7_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X0 : $i, X2 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.55  thf(t71_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.21/0.55           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.55  thf(t70_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.55  thf(t46_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.21/0.55           = (k2_xboole_0 @ (k1_enumset1 @ X16 @ X17 @ X18) @ (k1_tarski @ X19)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k2_tarski @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.55  thf(t69_enumset1, axiom,
% 0.21/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k2_tarski @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf(t11_setfam_1, axiom,
% 0.21/0.55    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.55  thf('14', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.21/0.55      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.55  thf(t10_setfam_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.55          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.21/0.55            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X30 : $i, X31 : $i]:
% 0.21/0.55         (((X30) = (k1_xboole_0))
% 0.21/0.55          | ((k1_setfam_1 @ (k2_xboole_0 @ X30 @ X31))
% 0.21/0.55              = (k3_xboole_0 @ (k1_setfam_1 @ X30) @ (k1_setfam_1 @ X31)))
% 0.21/0.55          | ((X31) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.21/0.55            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.21/0.55          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.55          | ((X1) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.21/0.55            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.21/0.55          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.21/0.55          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.55  thf('18', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.21/0.55      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.21/0.55          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.55         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.55        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.55        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.55        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.55  thf(l24_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (~ (r1_xboole_0 @ (k1_tarski @ X26) @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 0.21/0.55      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.55          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.55          | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_B @ k1_xboole_0)
% 0.21/0.55        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.55        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.55  thf(d1_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.55       ( ![E:$i]:
% 0.21/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_2, axiom,
% 0.21/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_3, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.55       ( ![E:$i]:
% 0.21/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.55         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.21/0.55          | (r2_hidden @ X9 @ X13)
% 0.21/0.55          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.55         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.21/0.55          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.21/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['28', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.21/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.55  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['27', '34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (((r2_hidden @ sk_B @ k1_xboole_0) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['26', '35'])).
% 0.21/0.55  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('clc', [status(thm)], ['25', '36'])).
% 0.21/0.55  thf('38', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.21/0.55      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.55  thf('39', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.55        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.55  thf('42', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.21/0.55      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.21/0.55        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (~ (r1_xboole_0 @ (k1_tarski @ X26) @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 0.21/0.55      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.55          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.21/0.55          | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_A @ k1_xboole_0)
% 0.21/0.55        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['40', '45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.21/0.55        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('48', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['27', '34'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.21/0.55        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('50', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['46', '49'])).
% 0.21/0.55  thf('51', plain, (((sk_A) = (sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['39', '50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.55  thf('53', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('clc', [status(thm)], ['25', '36'])).
% 0.21/0.55  thf('54', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('55', plain, (((sk_A) = (sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['39', '50'])).
% 0.21/0.55  thf('56', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.55  thf('57', plain, (((sk_A) != (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)],
% 0.21/0.55                ['0', '51', '52', '53', '54', '55', '56'])).
% 0.21/0.55  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
