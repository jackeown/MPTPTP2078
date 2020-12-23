%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jB8QzBTNl2

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:14 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 114 expanded)
%              Number of leaves         :   36 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  626 ( 884 expanded)
%              Number of equality atoms :   76 ( 110 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14','15','22'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['6','23','24'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('27',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('29',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X40 @ X39 @ X38 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X37 @ X35 @ X36 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X37 @ X35 @ X36 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('36',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['25','28','33','34','35'])).

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

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('40',plain,(
    ! [X29: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X31 )
      | ( X33 = X32 )
      | ( X33 = X29 )
      | ( X31
       != ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('41',plain,(
    ! [X29: $i,X32: $i,X33: $i] :
      ( ( X33 = X29 )
      | ( X33 = X32 )
      | ~ ( r2_hidden @ X33 @ ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X19 @ X20 @ X17 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jB8QzBTNl2
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 1657 iterations in 0.625s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.90/1.08  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.90/1.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.08  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(t25_zfmisc_1, conjecture,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.90/1.08          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.08        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.90/1.08             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.90/1.08  thf('0', plain,
% 0.90/1.08      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(t28_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      (![X8 : $i, X9 : $i]:
% 0.90/1.08         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.90/1.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.90/1.08         = (k1_tarski @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.08  thf(t100_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      (![X6 : $i, X7 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X6 @ X7)
% 0.90/1.08           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.90/1.08         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf(t98_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      (![X15 : $i, X16 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ X15 @ X16)
% 0.90/1.08           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.90/1.08         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ 
% 0.90/1.08            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.90/1.08         = (k1_tarski @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.08  thf(t48_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (![X10 : $i, X11 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.90/1.08           = (k3_xboole_0 @ X10 @ X11))),
% 0.90/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X10 : $i, X11 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.90/1.08           = (k3_xboole_0 @ X10 @ X11))),
% 0.90/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.08           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['8', '9'])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.90/1.08         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.90/1.08            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))))),
% 0.90/1.08      inference('sup+', [status(thm)], ['7', '10'])).
% 0.90/1.08  thf(idempotence_k3_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.90/1.08  thf('12', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.90/1.08      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      (![X6 : $i, X7 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X6 @ X7)
% 0.90/1.08           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['12', '13'])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.90/1.08         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['12', '13'])).
% 0.90/1.08  thf(t79_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.90/1.08      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.90/1.08  thf(d7_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.90/1.08       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X2 : $i, X3 : $i]:
% 0.90/1.08         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.90/1.08      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.08  thf(commutativity_k3_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.08  thf('21', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.90/1.08      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['16', '21'])).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.90/1.08      inference('demod', [status(thm)], ['11', '14', '15', '22'])).
% 0.90/1.08  thf(t5_boole, axiom,
% 0.90/1.08    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.08  thf('24', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.90/1.08      inference('cnf', [status(esa)], [t5_boole])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.90/1.08         = (k2_tarski @ sk_B @ sk_C))),
% 0.90/1.08      inference('demod', [status(thm)], ['6', '23', '24'])).
% 0.90/1.08  thf(t70_enumset1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (![X46 : $i, X47 : $i]:
% 0.90/1.08         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 0.90/1.08      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.08  thf(t46_enumset1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.90/1.08       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.90/1.08  thf('27', plain,
% 0.90/1.08      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.90/1.08         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 0.90/1.08           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.90/1.08           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['26', '27'])).
% 0.90/1.08  thf(t102_enumset1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.90/1.08  thf('29', plain,
% 0.90/1.08      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.90/1.08         ((k1_enumset1 @ X40 @ X39 @ X38) = (k1_enumset1 @ X38 @ X39 @ X40))),
% 0.90/1.08      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.90/1.08  thf(t100_enumset1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.90/1.08  thf('30', plain,
% 0.90/1.08      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.90/1.08         ((k1_enumset1 @ X37 @ X35 @ X36) = (k1_enumset1 @ X35 @ X36 @ X37))),
% 0.90/1.08      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['29', '30'])).
% 0.90/1.08  thf(t71_enumset1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.90/1.08         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 0.90/1.08           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 0.90/1.08      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['31', '32'])).
% 0.90/1.08  thf('34', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['29', '30'])).
% 0.90/1.08  thf('35', plain,
% 0.90/1.08      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.90/1.08         ((k1_enumset1 @ X37 @ X35 @ X36) = (k1_enumset1 @ X35 @ X36 @ X37))),
% 0.90/1.08      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.90/1.08      inference('demod', [status(thm)], ['25', '28', '33', '34', '35'])).
% 0.90/1.08  thf(d1_enumset1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.90/1.08       ( ![E:$i]:
% 0.90/1.08         ( ( r2_hidden @ E @ D ) <=>
% 0.90/1.08           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.90/1.08  thf(zf_stmt_2, axiom,
% 0.90/1.08    (![E:$i,C:$i,B:$i,A:$i]:
% 0.90/1.08     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.90/1.08       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_3, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.90/1.08       ( ![E:$i]:
% 0.90/1.08         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.90/1.08  thf('37', plain,
% 0.90/1.08      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.08         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.90/1.08          | (r2_hidden @ X22 @ X26)
% 0.90/1.08          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.08  thf('38', plain,
% 0.90/1.08      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.08         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 0.90/1.08          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 0.90/1.08      inference('simplify', [status(thm)], ['37'])).
% 0.90/1.08  thf('39', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.90/1.08          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.90/1.08      inference('sup+', [status(thm)], ['36', '38'])).
% 0.90/1.08  thf(d2_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.90/1.08       ( ![D:$i]:
% 0.90/1.08         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.90/1.08  thf('40', plain,
% 0.90/1.08      (![X29 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X33 @ X31)
% 0.90/1.08          | ((X33) = (X32))
% 0.90/1.08          | ((X33) = (X29))
% 0.90/1.08          | ((X31) != (k2_tarski @ X32 @ X29)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d2_tarski])).
% 0.90/1.08  thf('41', plain,
% 0.90/1.08      (![X29 : $i, X32 : $i, X33 : $i]:
% 0.90/1.08         (((X33) = (X29))
% 0.90/1.08          | ((X33) = (X32))
% 0.90/1.08          | ~ (r2_hidden @ X33 @ (k2_tarski @ X32 @ X29)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['40'])).
% 0.90/1.08  thf('42', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.90/1.08          | ((X0) = (sk_B))
% 0.90/1.08          | ((X0) = (sk_C)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['39', '41'])).
% 0.90/1.08  thf('43', plain,
% 0.90/1.08      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.08         (((X18) != (X17)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.08  thf('44', plain,
% 0.90/1.08      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.90/1.08         ~ (zip_tseitin_0 @ X17 @ X19 @ X20 @ X17)),
% 0.90/1.08      inference('simplify', [status(thm)], ['43'])).
% 0.90/1.08  thf('45', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['42', '44'])).
% 0.90/1.08  thf('46', plain, (((sk_A) != (sk_B))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('47', plain, (((sk_A) != (sk_C))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('48', plain, ($false),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['45', '46', '47'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
