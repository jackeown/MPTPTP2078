%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SeVEQmTUr6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:07 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 121 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  587 ( 852 expanded)
%              Number of equality atoms :   66 ( 105 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( X20 = X21 )
      | ( X20 = X22 )
      | ( X20 = X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('20',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('31',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
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

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X28 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X19 @ X21 @ X22 @ X19 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['30','43'])).

thf('45',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X25 @ X26 @ X27 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','51'])).

thf('53',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SeVEQmTUr6
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.57/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.80  % Solved by: fo/fo7.sh
% 0.57/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.80  % done 457 iterations in 0.357s
% 0.57/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.80  % SZS output start Refutation
% 0.57/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.57/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.57/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.80  thf(d1_enumset1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.57/0.80       ( ![E:$i]:
% 0.57/0.80         ( ( r2_hidden @ E @ D ) <=>
% 0.57/0.80           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.57/0.80  thf(zf_stmt_0, axiom,
% 0.57/0.80    (![E:$i,C:$i,B:$i,A:$i]:
% 0.57/0.80     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.57/0.80       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.57/0.80  thf('0', plain,
% 0.57/0.80      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.57/0.80         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.57/0.80          | ((X20) = (X21))
% 0.57/0.80          | ((X20) = (X22))
% 0.57/0.80          | ((X20) = (X23)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf(t13_zfmisc_1, conjecture,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.57/0.80         ( k1_tarski @ A ) ) =>
% 0.57/0.80       ( ( A ) = ( B ) ) ))).
% 0.57/0.80  thf(zf_stmt_1, negated_conjecture,
% 0.57/0.80    (~( ![A:$i,B:$i]:
% 0.57/0.80        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.57/0.80            ( k1_tarski @ A ) ) =>
% 0.57/0.80          ( ( A ) = ( B ) ) ) )),
% 0.57/0.80    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.57/0.80  thf('1', plain,
% 0.57/0.80      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.57/0.80         = (k1_tarski @ sk_A))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.80  thf(t98_xboole_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.57/0.80  thf('2', plain,
% 0.57/0.80      (![X17 : $i, X18 : $i]:
% 0.57/0.80         ((k2_xboole_0 @ X17 @ X18)
% 0.57/0.80           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.57/0.80  thf(t92_xboole_1, axiom,
% 0.57/0.80    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.57/0.80  thf('3', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.57/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.80  thf(t91_xboole_1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.80       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.57/0.80  thf('4', plain,
% 0.57/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.57/0.80           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.80  thf('5', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.80           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['3', '4'])).
% 0.57/0.80  thf(commutativity_k5_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.57/0.80  thf('6', plain,
% 0.57/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.80  thf(t5_boole, axiom,
% 0.57/0.80    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.80  thf('7', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.57/0.80      inference('cnf', [status(esa)], [t5_boole])).
% 0.57/0.80  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['6', '7'])).
% 0.57/0.80  thf('9', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.80      inference('demod', [status(thm)], ['5', '8'])).
% 0.57/0.80  thf('10', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.57/0.80           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['2', '9'])).
% 0.57/0.80  thf('11', plain,
% 0.57/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.57/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['1', '10'])).
% 0.57/0.80  thf('12', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.57/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.80  thf('13', plain,
% 0.57/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.57/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.80  thf(t100_xboole_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.80  thf('14', plain,
% 0.57/0.80      (![X8 : $i, X9 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X8 @ X9)
% 0.57/0.80           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.80  thf('15', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.80      inference('demod', [status(thm)], ['5', '8'])).
% 0.57/0.80  thf('16', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k3_xboole_0 @ X1 @ X0)
% 0.57/0.80           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['14', '15'])).
% 0.57/0.80  thf('17', plain,
% 0.57/0.80      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.57/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['13', '16'])).
% 0.57/0.80  thf('18', plain,
% 0.57/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.80  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['6', '7'])).
% 0.57/0.80  thf('20', plain,
% 0.57/0.80      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.57/0.80         = (k1_tarski @ sk_B))),
% 0.57/0.80      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.57/0.80  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.80  thf('21', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.80  thf('22', plain,
% 0.57/0.80      (![X8 : $i, X9 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X8 @ X9)
% 0.57/0.80           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.80  thf('23', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.57/0.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['21', '22'])).
% 0.57/0.80  thf('24', plain,
% 0.57/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.57/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['20', '23'])).
% 0.57/0.80  thf('25', plain,
% 0.57/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.80  thf('26', plain,
% 0.57/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.57/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.57/0.80      inference('demod', [status(thm)], ['24', '25'])).
% 0.57/0.80  thf('27', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.80      inference('demod', [status(thm)], ['5', '8'])).
% 0.57/0.80  thf('28', plain,
% 0.57/0.80      (((k1_tarski @ sk_A)
% 0.57/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.57/0.80            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.57/0.80      inference('sup+', [status(thm)], ['26', '27'])).
% 0.57/0.80  thf('29', plain,
% 0.57/0.80      (![X17 : $i, X18 : $i]:
% 0.57/0.80         ((k2_xboole_0 @ X17 @ X18)
% 0.57/0.80           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.57/0.80  thf('30', plain,
% 0.57/0.80      (((k1_tarski @ sk_A)
% 0.57/0.80         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.57/0.80      inference('demod', [status(thm)], ['28', '29'])).
% 0.57/0.80  thf(t69_enumset1, axiom,
% 0.57/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.80  thf('31', plain,
% 0.57/0.80      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.57/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.80  thf(t70_enumset1, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.57/0.80  thf('32', plain,
% 0.57/0.80      (![X32 : $i, X33 : $i]:
% 0.57/0.80         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.57/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.80  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.57/0.80  thf(zf_stmt_3, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.57/0.80       ( ![E:$i]:
% 0.57/0.80         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.57/0.80  thf('33', plain,
% 0.57/0.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.57/0.80         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.57/0.80          | (r2_hidden @ X24 @ X28)
% 0.57/0.80          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.80  thf('34', plain,
% 0.57/0.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.57/0.80         ((r2_hidden @ X24 @ (k1_enumset1 @ X27 @ X26 @ X25))
% 0.57/0.80          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27))),
% 0.57/0.80      inference('simplify', [status(thm)], ['33'])).
% 0.57/0.80  thf('35', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.57/0.80          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.57/0.80      inference('sup+', [status(thm)], ['32', '34'])).
% 0.57/0.80  thf('36', plain,
% 0.57/0.80      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.57/0.80         (((X20) != (X19)) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('37', plain,
% 0.57/0.80      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.57/0.80         ~ (zip_tseitin_0 @ X19 @ X21 @ X22 @ X19)),
% 0.57/0.80      inference('simplify', [status(thm)], ['36'])).
% 0.57/0.80  thf('38', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['35', '37'])).
% 0.57/0.80  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['31', '38'])).
% 0.57/0.80  thf(t7_xboole_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.57/0.80  thf('40', plain,
% 0.57/0.80      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.57/0.80      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.57/0.80  thf(d3_tarski, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.80  thf('41', plain,
% 0.57/0.80      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.57/0.80         (~ (r2_hidden @ X4 @ X5)
% 0.57/0.80          | (r2_hidden @ X4 @ X6)
% 0.57/0.80          | ~ (r1_tarski @ X5 @ X6))),
% 0.57/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.80  thf('42', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['40', '41'])).
% 0.57/0.80  thf('43', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['39', '42'])).
% 0.57/0.80  thf('44', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.57/0.80      inference('sup+', [status(thm)], ['30', '43'])).
% 0.57/0.80  thf('45', plain,
% 0.57/0.80      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.57/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.80  thf('46', plain,
% 0.57/0.80      (![X32 : $i, X33 : $i]:
% 0.57/0.80         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.57/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.80  thf('47', plain,
% 0.57/0.80      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.57/0.80         (~ (r2_hidden @ X29 @ X28)
% 0.57/0.80          | ~ (zip_tseitin_0 @ X29 @ X25 @ X26 @ X27)
% 0.57/0.80          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.80  thf('48', plain,
% 0.57/0.80      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 0.57/0.80         (~ (zip_tseitin_0 @ X29 @ X25 @ X26 @ X27)
% 0.57/0.80          | ~ (r2_hidden @ X29 @ (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.57/0.80      inference('simplify', [status(thm)], ['47'])).
% 0.57/0.80  thf('49', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.57/0.80          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['46', '48'])).
% 0.57/0.80  thf('50', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.57/0.80          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['45', '49'])).
% 0.57/0.80  thf('51', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.57/0.80      inference('sup-', [status(thm)], ['44', '50'])).
% 0.57/0.80  thf('52', plain,
% 0.57/0.80      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['0', '51'])).
% 0.57/0.80  thf('53', plain, (((sk_B) = (sk_A))),
% 0.57/0.80      inference('simplify', [status(thm)], ['52'])).
% 0.57/0.80  thf('54', plain, (((sk_A) != (sk_B))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.80  thf('55', plain, ($false),
% 0.57/0.80      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.57/0.80  
% 0.57/0.80  % SZS output end Refutation
% 0.57/0.80  
% 0.57/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
