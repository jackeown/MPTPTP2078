%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rZlGP6CdfH

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:55 EST 2020

% Result     : Theorem 2.56s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 116 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  604 ( 955 expanded)
%              Number of equality atoms :   54 (  87 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
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

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

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
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('48',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rZlGP6CdfH
% 0.17/0.37  % Computer   : n018.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 19:15:27 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 2.56/2.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.56/2.76  % Solved by: fo/fo7.sh
% 2.56/2.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.56/2.76  % done 2509 iterations in 2.282s
% 2.56/2.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.56/2.76  % SZS output start Refutation
% 2.56/2.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.56/2.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.56/2.76  thf(sk_B_type, type, sk_B: $i > $i).
% 2.56/2.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.56/2.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.56/2.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.56/2.76  thf(sk_A_type, type, sk_A: $i).
% 2.56/2.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.56/2.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.56/2.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.56/2.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.56/2.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.56/2.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.56/2.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.56/2.76  thf(t65_zfmisc_1, conjecture,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.56/2.76       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.56/2.76  thf(zf_stmt_0, negated_conjecture,
% 2.56/2.76    (~( ![A:$i,B:$i]:
% 2.56/2.76        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.56/2.76          ( ~( r2_hidden @ B @ A ) ) ) )),
% 2.56/2.76    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 2.56/2.76  thf('0', plain,
% 2.56/2.76      (((r2_hidden @ sk_B_1 @ sk_A)
% 2.56/2.76        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('1', plain,
% 2.56/2.76      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 2.56/2.76       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 2.56/2.76      inference('split', [status(esa)], ['0'])).
% 2.56/2.76  thf('2', plain,
% 2.56/2.76      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 2.56/2.76      inference('split', [status(esa)], ['0'])).
% 2.56/2.76  thf(t70_enumset1, axiom,
% 2.56/2.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.56/2.76  thf('3', plain,
% 2.56/2.76      (![X29 : $i, X30 : $i]:
% 2.56/2.76         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 2.56/2.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.56/2.76  thf(d1_enumset1, axiom,
% 2.56/2.76    (![A:$i,B:$i,C:$i,D:$i]:
% 2.56/2.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.56/2.76       ( ![E:$i]:
% 2.56/2.76         ( ( r2_hidden @ E @ D ) <=>
% 2.56/2.76           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.56/2.76  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.56/2.76  thf(zf_stmt_2, axiom,
% 2.56/2.76    (![E:$i,C:$i,B:$i,A:$i]:
% 2.56/2.76     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.56/2.76       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.56/2.76  thf(zf_stmt_3, axiom,
% 2.56/2.76    (![A:$i,B:$i,C:$i,D:$i]:
% 2.56/2.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.56/2.76       ( ![E:$i]:
% 2.56/2.76         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.56/2.76  thf('4', plain,
% 2.56/2.76      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.56/2.76         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 2.56/2.76          | (r2_hidden @ X21 @ X25)
% 2.56/2.76          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.56/2.76  thf('5', plain,
% 2.56/2.76      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.56/2.76         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 2.56/2.76          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 2.56/2.76      inference('simplify', [status(thm)], ['4'])).
% 2.56/2.76  thf('6', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.76         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.56/2.76          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.56/2.76      inference('sup+', [status(thm)], ['3', '5'])).
% 2.56/2.76  thf('7', plain,
% 2.56/2.76      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.56/2.76         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.56/2.76  thf('8', plain,
% 2.56/2.76      (![X16 : $i, X18 : $i, X19 : $i]:
% 2.56/2.76         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 2.56/2.76      inference('simplify', [status(thm)], ['7'])).
% 2.56/2.76  thf('9', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.56/2.76      inference('sup-', [status(thm)], ['6', '8'])).
% 2.56/2.76  thf(t69_enumset1, axiom,
% 2.56/2.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.56/2.76  thf('10', plain,
% 2.56/2.76      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 2.56/2.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.56/2.76  thf(d5_xboole_0, axiom,
% 2.56/2.76    (![A:$i,B:$i,C:$i]:
% 2.56/2.76     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.56/2.76       ( ![D:$i]:
% 2.56/2.76         ( ( r2_hidden @ D @ C ) <=>
% 2.56/2.76           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.56/2.76  thf('11', plain,
% 2.56/2.76      (![X3 : $i, X4 : $i, X7 : $i]:
% 2.56/2.76         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 2.56/2.76          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 2.56/2.76          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 2.56/2.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.56/2.76  thf('12', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.56/2.76          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.56/2.76      inference('eq_fact', [status(thm)], ['11'])).
% 2.56/2.76  thf('13', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.56/2.76          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.56/2.76      inference('eq_fact', [status(thm)], ['11'])).
% 2.56/2.76  thf(l27_zfmisc_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.56/2.76  thf('14', plain,
% 2.56/2.76      (![X38 : $i, X39 : $i]:
% 2.56/2.76         ((r1_xboole_0 @ (k1_tarski @ X38) @ X39) | (r2_hidden @ X38 @ X39))),
% 2.56/2.76      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.56/2.76  thf(t7_xboole_0, axiom,
% 2.56/2.76    (![A:$i]:
% 2.56/2.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.56/2.76          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.56/2.76  thf('15', plain,
% 2.56/2.76      (![X12 : $i]:
% 2.56/2.76         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 2.56/2.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.56/2.76  thf(t4_xboole_0, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.56/2.76            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.56/2.76       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.56/2.76            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.56/2.76  thf('16', plain,
% 2.56/2.76      (![X8 : $i, X10 : $i, X11 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 2.56/2.76          | ~ (r1_xboole_0 @ X8 @ X11))),
% 2.56/2.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.56/2.76  thf('17', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['15', '16'])).
% 2.56/2.76  thf('18', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         ((r2_hidden @ X1 @ X0)
% 2.56/2.76          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['14', '17'])).
% 2.56/2.76  thf(commutativity_k3_xboole_0, axiom,
% 2.56/2.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.56/2.76  thf('19', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.56/2.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.56/2.76  thf(t100_xboole_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.56/2.76  thf('20', plain,
% 2.56/2.76      (![X13 : $i, X14 : $i]:
% 2.56/2.76         ((k4_xboole_0 @ X13 @ X14)
% 2.56/2.76           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.56/2.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.56/2.76  thf('21', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         ((k4_xboole_0 @ X0 @ X1)
% 2.56/2.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.56/2.76      inference('sup+', [status(thm)], ['19', '20'])).
% 2.56/2.76  thf('22', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 2.56/2.76            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.56/2.76          | (r2_hidden @ X1 @ X0))),
% 2.56/2.76      inference('sup+', [status(thm)], ['18', '21'])).
% 2.56/2.76  thf(t5_boole, axiom,
% 2.56/2.76    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.56/2.76  thf('23', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 2.56/2.76      inference('cnf', [status(esa)], [t5_boole])).
% 2.56/2.76  thf('24', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 2.56/2.76          | (r2_hidden @ X1 @ X0))),
% 2.56/2.76      inference('demod', [status(thm)], ['22', '23'])).
% 2.56/2.76  thf('25', plain,
% 2.56/2.76      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X6 @ X5)
% 2.56/2.76          | ~ (r2_hidden @ X6 @ X4)
% 2.56/2.76          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.56/2.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.56/2.76  thf('26', plain,
% 2.56/2.76      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X6 @ X4)
% 2.56/2.76          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.56/2.76      inference('simplify', [status(thm)], ['25'])).
% 2.56/2.76  thf('27', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X2 @ X0)
% 2.56/2.76          | (r2_hidden @ X1 @ X0)
% 2.56/2.76          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['24', '26'])).
% 2.56/2.76  thf('28', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.76         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 2.56/2.76          | (r2_hidden @ X0 @ X2)
% 2.56/2.76          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 2.56/2.76               X2))),
% 2.56/2.76      inference('sup-', [status(thm)], ['13', '27'])).
% 2.56/2.76  thf('29', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 2.56/2.76          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 2.56/2.76          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['12', '28'])).
% 2.56/2.76  thf('30', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 2.56/2.76          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 2.56/2.76      inference('simplify', [status(thm)], ['29'])).
% 2.56/2.76  thf('31', plain,
% 2.56/2.76      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X6 @ X4)
% 2.56/2.76          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.56/2.76      inference('simplify', [status(thm)], ['25'])).
% 2.56/2.76  thf('32', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 2.56/2.76          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 2.56/2.76          | ~ (r2_hidden @ X2 @ X1))),
% 2.56/2.76      inference('sup-', [status(thm)], ['30', '31'])).
% 2.56/2.76  thf('33', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.56/2.76          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.56/2.76      inference('condensation', [status(thm)], ['32'])).
% 2.56/2.76  thf('34', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 2.56/2.76          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['10', '33'])).
% 2.56/2.76  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['9', '34'])).
% 2.56/2.76  thf('36', plain,
% 2.56/2.76      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 2.56/2.76        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('37', plain,
% 2.56/2.76      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 2.56/2.76         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.56/2.76      inference('split', [status(esa)], ['36'])).
% 2.56/2.76  thf('38', plain,
% 2.56/2.76      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.56/2.76         (~ (r2_hidden @ X6 @ X4)
% 2.56/2.76          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.56/2.76      inference('simplify', [status(thm)], ['25'])).
% 2.56/2.76  thf('39', plain,
% 2.56/2.76      ((![X0 : $i]:
% 2.56/2.76          (~ (r2_hidden @ X0 @ sk_A)
% 2.56/2.76           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1))))
% 2.56/2.76         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['37', '38'])).
% 2.56/2.76  thf('40', plain,
% 2.56/2.76      ((~ (r2_hidden @ sk_B_1 @ sk_A))
% 2.56/2.76         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['35', '39'])).
% 2.56/2.76  thf('41', plain,
% 2.56/2.76      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 2.56/2.76       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['2', '40'])).
% 2.56/2.76  thf('42', plain,
% 2.56/2.76      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 2.56/2.76       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 2.56/2.76      inference('split', [status(esa)], ['36'])).
% 2.56/2.76  thf('43', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 2.56/2.76          | (r2_hidden @ X1 @ X0))),
% 2.56/2.76      inference('demod', [status(thm)], ['22', '23'])).
% 2.56/2.76  thf('44', plain,
% 2.56/2.76      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 2.56/2.76         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.56/2.76      inference('split', [status(esa)], ['0'])).
% 2.56/2.76  thf('45', plain,
% 2.56/2.76      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A)))
% 2.56/2.76         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['43', '44'])).
% 2.56/2.76  thf('46', plain,
% 2.56/2.76      (((r2_hidden @ sk_B_1 @ sk_A))
% 2.56/2.76         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.56/2.76      inference('simplify', [status(thm)], ['45'])).
% 2.56/2.76  thf('47', plain,
% 2.56/2.76      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 2.56/2.76      inference('split', [status(esa)], ['36'])).
% 2.56/2.76  thf('48', plain,
% 2.56/2.76      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 2.56/2.76       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['46', '47'])).
% 2.56/2.76  thf('49', plain, ($false),
% 2.56/2.76      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '48'])).
% 2.56/2.76  
% 2.56/2.76  % SZS output end Refutation
% 2.56/2.76  
% 2.56/2.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
