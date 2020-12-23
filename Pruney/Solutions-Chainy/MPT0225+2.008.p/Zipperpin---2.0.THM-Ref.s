%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m3seHe6nC1

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:45 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 122 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  635 (1083 expanded)
%              Number of equality atoms :   91 ( 168 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('0',plain,
    ( ( sk_A = sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('9',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
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

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('30',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','32'])).

thf('34',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('35',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X58 ) @ ( k1_tarski @ X59 ) )
      | ( X58 = X59 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( sk_B_1 = sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B_1 = sk_A )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A != sk_B_1 )
   <= ( sk_A != sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('48',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_A != sk_B_1 )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m3seHe6nC1
% 0.18/0.37  % Computer   : n011.cluster.edu
% 0.18/0.37  % Model      : x86_64 x86_64
% 0.18/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.37  % Memory     : 8042.1875MB
% 0.18/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.37  % CPULimit   : 60
% 0.18/0.37  % DateTime   : Tue Dec  1 20:30:42 EST 2020
% 0.18/0.37  % CPUTime    : 
% 0.18/0.37  % Running portfolio for 600 s
% 0.18/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.37  % Number of cores: 8
% 0.18/0.38  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 608 iterations in 0.129s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.60  thf(t20_zfmisc_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.39/0.60         ( k1_tarski @ A ) ) <=>
% 0.39/0.60       ( ( A ) != ( B ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i]:
% 0.39/0.60        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.39/0.60            ( k1_tarski @ A ) ) <=>
% 0.39/0.60          ( ( A ) != ( B ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      ((((sk_A) = (sk_B_1))
% 0.39/0.60        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60            != (k1_tarski @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      ((((sk_A) = (sk_B_1))) | 
% 0.39/0.60       ~
% 0.39/0.60       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60          = (k1_tarski @ sk_A)))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf('2', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      ((((sk_A) != (sk_B_1))
% 0.39/0.60        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60            = (k1_tarski @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60          = (k1_tarski @ sk_A)))
% 0.39/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60                = (k1_tarski @ sk_A))))),
% 0.39/0.60      inference('split', [status(esa)], ['3'])).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.39/0.60          = (k1_tarski @ sk_A)))
% 0.39/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60                = (k1_tarski @ sk_A))) & 
% 0.39/0.60             (((sk_A) = (sk_B_1))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['2', '4'])).
% 0.39/0.60  thf('6', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.39/0.60          = (k1_tarski @ sk_B_1)))
% 0.39/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60                = (k1_tarski @ sk_A))) & 
% 0.39/0.60             (((sk_A) = (sk_B_1))))),
% 0.39/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.60  thf(t79_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.39/0.60      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (((r1_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1)))
% 0.39/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60                = (k1_tarski @ sk_A))) & 
% 0.39/0.60             (((sk_A) = (sk_B_1))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.60  thf(d7_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      ((((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.39/0.60          = (k1_xboole_0)))
% 0.39/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60                = (k1_tarski @ sk_A))) & 
% 0.39/0.60             (((sk_A) = (sk_B_1))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.60  thf('12', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.39/0.60         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.60                = (k1_tarski @ sk_A))) & 
% 0.39/0.60             (((sk_A) = (sk_B_1))))),
% 0.39/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.60  thf(t69_enumset1, axiom,
% 0.39/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.39/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.60  thf(t70_enumset1, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (![X31 : $i, X32 : $i]:
% 0.39/0.60         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.39/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.61  thf(d1_enumset1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.61       ( ![E:$i]:
% 0.39/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.39/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.39/0.61  thf(zf_stmt_2, axiom,
% 0.39/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.39/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.39/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_3, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.61       ( ![E:$i]:
% 0.39/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.61         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 0.39/0.61          | (r2_hidden @ X23 @ X27)
% 0.39/0.61          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.61         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 0.39/0.61          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 0.39/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.39/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['15', '17'])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.61         (((X19) != (X18)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.39/0.61         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X18)),
% 0.39/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['18', '20'])).
% 0.39/0.61  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['14', '21'])).
% 0.39/0.61  thf('23', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.61  thf(t4_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.61            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.39/0.61          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['22', '25'])).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.39/0.61         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61                = (k1_tarski @ sk_A))) & 
% 0.39/0.61             (((sk_A) = (sk_B_1))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['13', '26'])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.39/0.61         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61                = (k1_tarski @ sk_A))) & 
% 0.39/0.61             (((sk_A) = (sk_B_1))))),
% 0.39/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.39/0.61  thf('29', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      (![X2 : $i, X4 : $i]:
% 0.39/0.61         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.61  thf('32', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.39/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (~ (((sk_A) = (sk_B_1))) | 
% 0.39/0.61       ~
% 0.39/0.61       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61          = (k1_tarski @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['27', '28', '32'])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (~ (((sk_A) = (sk_B_1))) | 
% 0.39/0.61       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61          = (k1_tarski @ sk_A)))),
% 0.39/0.61      inference('split', [status(esa)], ['3'])).
% 0.39/0.61  thf(t17_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( A ) != ( B ) ) =>
% 0.39/0.61       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.39/0.61  thf('35', plain,
% 0.39/0.61      (![X58 : $i, X59 : $i]:
% 0.39/0.61         ((r1_xboole_0 @ (k1_tarski @ X58) @ (k1_tarski @ X59))
% 0.39/0.61          | ((X58) = (X59)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.39/0.61  thf('36', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]:
% 0.39/0.61         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((X1) = (X0))
% 0.39/0.61          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.39/0.61              = (k1_xboole_0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.61  thf(t100_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (![X13 : $i, X14 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X13 @ X14)
% 0.39/0.61           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.61  thf('40', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.39/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['38', '39'])).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.39/0.61            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.39/0.61          | ((X1) = (X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['37', '40'])).
% 0.39/0.61  thf(t5_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.61  thf('42', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.39/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.39/0.61            = (k1_tarski @ X0))
% 0.39/0.61          | ((X1) = (X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.61  thf('44', plain,
% 0.39/0.61      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61          != (k1_tarski @ sk_A)))
% 0.39/0.61         <= (~
% 0.39/0.61             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61                = (k1_tarski @ sk_A))))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('45', plain,
% 0.39/0.61      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | ((sk_B_1) = (sk_A))))
% 0.39/0.61         <= (~
% 0.39/0.61             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61                = (k1_tarski @ sk_A))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.61  thf('46', plain,
% 0.39/0.61      ((((sk_B_1) = (sk_A)))
% 0.39/0.61         <= (~
% 0.39/0.61             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61                = (k1_tarski @ sk_A))))),
% 0.39/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.39/0.61  thf('47', plain, ((((sk_A) != (sk_B_1))) <= (~ (((sk_A) = (sk_B_1))))),
% 0.39/0.61      inference('split', [status(esa)], ['3'])).
% 0.39/0.61  thf('48', plain,
% 0.39/0.61      ((((sk_B_1) != (sk_B_1)))
% 0.39/0.61         <= (~ (((sk_A) = (sk_B_1))) & 
% 0.39/0.61             ~
% 0.39/0.61             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61                = (k1_tarski @ sk_A))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.61  thf('49', plain,
% 0.39/0.61      ((((sk_A) = (sk_B_1))) | 
% 0.39/0.61       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.39/0.61          = (k1_tarski @ sk_A)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.61  thf('50', plain, ($false),
% 0.39/0.61      inference('sat_resolution*', [status(thm)], ['1', '33', '34', '49'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
