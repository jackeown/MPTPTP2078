%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dfFqp4miDV

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:34 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   87 (  95 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  600 ( 666 expanded)
%              Number of equality atoms :   70 (  80 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','11'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('30',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X40 @ X41 @ X42 ) @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('33',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( k2_enumset1 @ X47 @ X47 @ X48 @ X49 )
      = ( k1_enumset1 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k2_tarski @ sk_B_1 @ sk_A )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
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

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X22 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('46',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ X34 )
      | ( X35 = X32 )
      | ( X34
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X32: $i,X35: $i] :
      ( ( X35 = X32 )
      | ~ ( r2_hidden @ X35 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dfFqp4miDV
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 1114 iterations in 0.434s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.89  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.68/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.89  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.68/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.68/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.68/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(t18_zfmisc_1, conjecture,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.68/0.89         ( k1_tarski @ A ) ) =>
% 0.68/0.89       ( ( A ) = ( B ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i,B:$i]:
% 0.68/0.89        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.68/0.89            ( k1_tarski @ A ) ) =>
% 0.68/0.89          ( ( A ) = ( B ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.68/0.89         = (k1_tarski @ sk_A))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.68/0.89         = (k1_tarski @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.89  thf('3', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.89  thf(t100_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.89  thf('4', plain,
% 0.68/0.89      (![X7 : $i, X8 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X7 @ X8)
% 0.68/0.89           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['3', '4'])).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.68/0.89         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['2', '5'])).
% 0.68/0.89  thf(t21_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      (![X9 : $i, X10 : $i]:
% 0.68/0.89         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.68/0.89      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.68/0.89  thf('8', plain,
% 0.68/0.89      (![X7 : $i, X8 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X7 @ X8)
% 0.68/0.89           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.89  thf('9', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.68/0.89           = (k5_xboole_0 @ X0 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['7', '8'])).
% 0.68/0.89  thf(t46_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      (![X13 : $i, X14 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.68/0.89      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.68/0.89  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.68/0.89         = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['6', '11'])).
% 0.68/0.89  thf(t79_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.68/0.89  thf('13', plain,
% 0.68/0.89      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.68/0.89      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.68/0.89  thf(t7_xboole_0, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.68/0.89          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.68/0.89      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.68/0.89  thf(t4_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.89            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.89       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.68/0.89            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.68/0.89          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.68/0.89      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.89  thf('17', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['13', '16'])).
% 0.68/0.89  thf('18', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['17', '18'])).
% 0.68/0.89  thf(t94_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k2_xboole_0 @ A @ B ) =
% 0.68/0.89       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.89  thf('20', plain,
% 0.68/0.89      (![X18 : $i, X19 : $i]:
% 0.68/0.89         ((k2_xboole_0 @ X18 @ X19)
% 0.68/0.89           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.68/0.89              (k3_xboole_0 @ X18 @ X19)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.89           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.68/0.89              k1_xboole_0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['19', '20'])).
% 0.68/0.89  thf(t39_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.89  thf('22', plain,
% 0.68/0.89      (![X11 : $i, X12 : $i]:
% 0.68/0.89         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.68/0.89           = (k2_xboole_0 @ X11 @ X12))),
% 0.68/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.68/0.89  thf(t5_boole, axiom,
% 0.68/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.89  thf('23', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.68/0.89      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.89  thf('24', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k2_xboole_0 @ X0 @ X1)
% 0.68/0.89           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.68/0.89      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.68/0.89  thf('25', plain,
% 0.68/0.89      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.68/0.89         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['12', '24'])).
% 0.68/0.89  thf('26', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.68/0.89      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.89  thf('27', plain,
% 0.68/0.89      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.68/0.89         = (k1_tarski @ sk_B_1))),
% 0.68/0.89      inference('demod', [status(thm)], ['25', '26'])).
% 0.68/0.89  thf(t69_enumset1, axiom,
% 0.68/0.89    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.68/0.89  thf('28', plain,
% 0.68/0.89      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.68/0.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.89  thf(t70_enumset1, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.68/0.89  thf('29', plain,
% 0.68/0.89      (![X45 : $i, X46 : $i]:
% 0.68/0.89         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.68/0.89      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.89  thf(t46_enumset1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.89     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.68/0.89       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.68/0.89  thf('30', plain,
% 0.68/0.89      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.68/0.89         ((k2_enumset1 @ X40 @ X41 @ X42 @ X43)
% 0.68/0.89           = (k2_xboole_0 @ (k1_enumset1 @ X40 @ X41 @ X42) @ (k1_tarski @ X43)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.68/0.89           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['29', '30'])).
% 0.68/0.89  thf('32', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.68/0.89           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['28', '31'])).
% 0.68/0.89  thf(t71_enumset1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.68/0.89  thf('33', plain,
% 0.68/0.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.68/0.89         ((k2_enumset1 @ X47 @ X47 @ X48 @ X49)
% 0.68/0.89           = (k1_enumset1 @ X47 @ X48 @ X49))),
% 0.68/0.89      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.89  thf('34', plain,
% 0.68/0.89      (![X45 : $i, X46 : $i]:
% 0.68/0.89         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.68/0.89      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.89  thf('35', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['33', '34'])).
% 0.68/0.89  thf('36', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k2_tarski @ X0 @ X1)
% 0.68/0.89           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.68/0.89      inference('demod', [status(thm)], ['32', '35'])).
% 0.68/0.89  thf('37', plain, (((k2_tarski @ sk_B_1 @ sk_A) = (k1_tarski @ sk_B_1))),
% 0.68/0.89      inference('demod', [status(thm)], ['27', '36'])).
% 0.68/0.89  thf('38', plain,
% 0.68/0.89      (![X45 : $i, X46 : $i]:
% 0.68/0.89         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.68/0.89      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.89  thf(d1_enumset1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.68/0.89       ( ![E:$i]:
% 0.68/0.89         ( ( r2_hidden @ E @ D ) <=>
% 0.68/0.89           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.68/0.89  thf(zf_stmt_2, axiom,
% 0.68/0.89    (![E:$i,C:$i,B:$i,A:$i]:
% 0.68/0.89     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.68/0.89       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_3, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.68/0.89       ( ![E:$i]:
% 0.68/0.89         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.68/0.89  thf('39', plain,
% 0.68/0.89      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.68/0.89         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.68/0.89          | (r2_hidden @ X25 @ X29)
% 0.68/0.89          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.89  thf('40', plain,
% 0.68/0.89      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.68/0.89         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 0.68/0.89          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 0.68/0.89      inference('simplify', [status(thm)], ['39'])).
% 0.68/0.89  thf('41', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.68/0.89          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.68/0.89      inference('sup+', [status(thm)], ['38', '40'])).
% 0.68/0.89  thf('42', plain,
% 0.68/0.89      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.68/0.89         (((X21) != (X22)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.89  thf('43', plain,
% 0.68/0.89      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.68/0.89         ~ (zip_tseitin_0 @ X22 @ X22 @ X23 @ X20)),
% 0.68/0.89      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.89  thf('44', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['41', '43'])).
% 0.68/0.89  thf('45', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.68/0.89      inference('sup+', [status(thm)], ['37', '44'])).
% 0.68/0.89  thf(d1_tarski, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.68/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.68/0.89  thf('46', plain,
% 0.68/0.89      (![X32 : $i, X34 : $i, X35 : $i]:
% 0.68/0.89         (~ (r2_hidden @ X35 @ X34)
% 0.68/0.89          | ((X35) = (X32))
% 0.68/0.89          | ((X34) != (k1_tarski @ X32)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d1_tarski])).
% 0.68/0.89  thf('47', plain,
% 0.68/0.89      (![X32 : $i, X35 : $i]:
% 0.68/0.89         (((X35) = (X32)) | ~ (r2_hidden @ X35 @ (k1_tarski @ X32)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['46'])).
% 0.68/0.89  thf('48', plain, (((sk_A) = (sk_B_1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['45', '47'])).
% 0.68/0.89  thf('49', plain, (((sk_A) != (sk_B_1))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('50', plain, ($false),
% 0.68/0.89      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.68/0.89  
% 0.68/0.89  % SZS output end Refutation
% 0.68/0.89  
% 0.68/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
