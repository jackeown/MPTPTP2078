%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8hxRPeDjSg

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:15 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   84 (  99 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  568 ( 704 expanded)
%              Number of equality atoms :   69 (  88 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X27 @ X28 @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_enumset1 @ X34 @ X34 @ X35 @ X36 )
      = ( k1_enumset1 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['28','33'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X17 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8hxRPeDjSg
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 496 iterations in 0.222s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(d1_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.67       ( ![E:$i]:
% 0.45/0.67         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.67           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, axiom,
% 0.45/0.67    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.67       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.45/0.67          | ((X16) = (X17))
% 0.45/0.67          | ((X16) = (X18))
% 0.45/0.67          | ((X16) = (X19)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t25_zfmisc_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.45/0.67          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_1, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.67        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.45/0.67             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.67  thf(t28_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X7 : $i, X8 : $i]:
% 0.45/0.67         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.45/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.45/0.67         = (k1_tarski @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf(t100_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X3 @ X4)
% 0.45/0.67           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.45/0.67         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf(t17_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.45/0.67      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.67  thf(t3_xboole_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X3 @ X4)
% 0.45/0.67           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['8', '11'])).
% 0.45/0.67  thf(t5_boole, axiom,
% 0.45/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.67  thf('13', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.67  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf(t48_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X10 : $i, X11 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.45/0.67           = (k3_xboole_0 @ X10 @ X11))),
% 0.45/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.67  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.67  thf('17', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X3 @ X4)
% 0.45/0.67           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.45/0.67         = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['5', '23'])).
% 0.45/0.67  thf(t98_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X13 : $i, X14 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ X13 @ X14)
% 0.45/0.67           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.45/0.67         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf('27', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.45/0.67         = (k2_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf(t70_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X32 : $i, X33 : $i]:
% 0.45/0.67         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.45/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.67  thf(t46_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.45/0.67       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.67         ((k2_enumset1 @ X27 @ X28 @ X29 @ X30)
% 0.45/0.67           = (k2_xboole_0 @ (k1_enumset1 @ X27 @ X28 @ X29) @ (k1_tarski @ X30)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.45/0.67           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf(t71_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.67         ((k2_enumset1 @ X34 @ X34 @ X35 @ X36)
% 0.45/0.67           = (k1_enumset1 @ X34 @ X35 @ X36))),
% 0.45/0.67      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.45/0.67           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['31', '32'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (((k1_enumset1 @ sk_B @ sk_C @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['28', '33'])).
% 0.45/0.67  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_3, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.67       ( ![E:$i]:
% 0.45/0.67         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.45/0.67          | (r2_hidden @ X20 @ X24)
% 0.45/0.67          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.67         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.45/0.67          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.45/0.67      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.45/0.67          | (zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['34', '36'])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.67         (((X16) != (X17)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.45/0.67         ~ (zip_tseitin_0 @ X17 @ X17 @ X18 @ X15)),
% 0.45/0.67      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.67  thf('40', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['37', '39'])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X32 : $i, X33 : $i]:
% 0.45/0.67         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.45/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X25 @ X24)
% 0.45/0.67          | ~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.45/0.67          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.45/0.67         (~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.45/0.67          | ~ (r2_hidden @ X25 @ (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['42'])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.67          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['41', '43'])).
% 0.45/0.67  thf('45', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.45/0.67      inference('sup-', [status(thm)], ['40', '44'])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '45'])).
% 0.45/0.67  thf('47', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.67  thf('48', plain, (((sk_A) != (sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.67  thf('49', plain, (((sk_A) != (sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.67  thf('50', plain, ($false),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['47', '48', '49'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
