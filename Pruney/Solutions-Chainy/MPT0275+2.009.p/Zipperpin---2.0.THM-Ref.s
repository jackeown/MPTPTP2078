%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.la2N1FVcKc

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:37 EST 2020

% Result     : Theorem 22.02s
% Output     : Refutation 22.02s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 189 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          : 1053 (1800 expanded)
%              Number of equality atoms :   76 ( 133 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
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

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X36 )
      | ( X36
       != ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ ( k1_enumset1 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X29 )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X29 @ X29 @ X30 @ X27 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X12 ) )
      | ( r2_hidden @ X9 @ X12 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) @ ( k5_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) @ ( k5_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('23',plain,(
    ! [X26: $i] :
      ( r1_xboole_0 @ X26 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['37'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('43',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X59 @ X60 )
      | ~ ( r2_hidden @ X61 @ X60 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X59 @ X61 ) @ X60 )
        = ( k2_tarski @ X59 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C_1 )
          = ( k2_tarski @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ X0 ) )
          = ( k2_tarski @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( r2_hidden @ sk_A @ sk_C_1 )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ sk_C_1 )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ sk_C_1 )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','59'])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_C_1 )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('68',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X27 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X12 ) )
      | ( r2_hidden @ X9 @ X12 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) @ ( k5_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) @ ( k5_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','77'])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('84',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['37'])).

thf('86',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','63','64','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.la2N1FVcKc
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.33  % CPULimit   : 60
% 0.20/0.33  % DateTime   : Tue Dec  1 14:18:12 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 22.02/22.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 22.02/22.27  % Solved by: fo/fo7.sh
% 22.02/22.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.02/22.27  % done 10777 iterations in 21.822s
% 22.02/22.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 22.02/22.27  % SZS output start Refutation
% 22.02/22.27  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 22.02/22.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 22.02/22.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 22.02/22.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 22.02/22.27  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 22.02/22.27  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 22.02/22.27  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 22.02/22.27  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 22.02/22.27  thf(sk_A_type, type, sk_A: $i).
% 22.02/22.27  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 22.02/22.27  thf(sk_B_type, type, sk_B: $i).
% 22.02/22.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 22.02/22.27  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 22.02/22.27  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 22.02/22.27  thf(t73_zfmisc_1, conjecture,
% 22.02/22.27    (![A:$i,B:$i,C:$i]:
% 22.02/22.27     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 22.02/22.27       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 22.02/22.27  thf(zf_stmt_0, negated_conjecture,
% 22.02/22.27    (~( ![A:$i,B:$i,C:$i]:
% 22.02/22.27        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 22.02/22.27          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 22.02/22.27    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 22.02/22.27  thf('0', plain,
% 22.02/22.27      (((r2_hidden @ sk_B @ sk_C_1)
% 22.02/22.27        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 22.02/22.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.27  thf('1', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 22.02/22.27       ((r2_hidden @ sk_B @ sk_C_1))),
% 22.02/22.27      inference('split', [status(esa)], ['0'])).
% 22.02/22.27  thf('2', plain,
% 22.02/22.27      (((r2_hidden @ sk_A @ sk_C_1)
% 22.02/22.27        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 22.02/22.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.27  thf('3', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('split', [status(esa)], ['2'])).
% 22.02/22.27  thf(t100_xboole_1, axiom,
% 22.02/22.27    (![A:$i,B:$i]:
% 22.02/22.27     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 22.02/22.27  thf('4', plain,
% 22.02/22.27      (![X23 : $i, X24 : $i]:
% 22.02/22.27         ((k4_xboole_0 @ X23 @ X24)
% 22.02/22.27           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 22.02/22.27      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.27  thf(t70_enumset1, axiom,
% 22.02/22.27    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 22.02/22.27  thf('5', plain,
% 22.02/22.27      (![X39 : $i, X40 : $i]:
% 22.02/22.27         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 22.02/22.27      inference('cnf', [status(esa)], [t70_enumset1])).
% 22.02/22.27  thf(d1_enumset1, axiom,
% 22.02/22.27    (![A:$i,B:$i,C:$i,D:$i]:
% 22.02/22.27     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 22.02/22.27       ( ![E:$i]:
% 22.02/22.27         ( ( r2_hidden @ E @ D ) <=>
% 22.02/22.27           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 22.02/22.27  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 22.02/22.27  thf(zf_stmt_2, axiom,
% 22.02/22.27    (![E:$i,C:$i,B:$i,A:$i]:
% 22.02/22.27     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 22.02/22.27       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 22.02/22.27  thf(zf_stmt_3, axiom,
% 22.02/22.27    (![A:$i,B:$i,C:$i,D:$i]:
% 22.02/22.27     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 22.02/22.27       ( ![E:$i]:
% 22.02/22.27         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 22.02/22.27  thf('6', plain,
% 22.02/22.27      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 22.02/22.27         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35)
% 22.02/22.27          | (r2_hidden @ X32 @ X36)
% 22.02/22.27          | ((X36) != (k1_enumset1 @ X35 @ X34 @ X33)))),
% 22.02/22.27      inference('cnf', [status(esa)], [zf_stmt_3])).
% 22.02/22.27  thf('7', plain,
% 22.02/22.27      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 22.02/22.27         ((r2_hidden @ X32 @ (k1_enumset1 @ X35 @ X34 @ X33))
% 22.02/22.27          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35))),
% 22.02/22.27      inference('simplify', [status(thm)], ['6'])).
% 22.02/22.27  thf('8', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 22.02/22.27          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 22.02/22.27      inference('sup+', [status(thm)], ['5', '7'])).
% 22.02/22.27  thf('9', plain,
% 22.02/22.27      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 22.02/22.27         (((X28) != (X29)) | ~ (zip_tseitin_0 @ X28 @ X29 @ X30 @ X27))),
% 22.02/22.27      inference('cnf', [status(esa)], [zf_stmt_2])).
% 22.02/22.27  thf('10', plain,
% 22.02/22.27      (![X27 : $i, X29 : $i, X30 : $i]:
% 22.02/22.27         ~ (zip_tseitin_0 @ X29 @ X29 @ X30 @ X27)),
% 22.02/22.27      inference('simplify', [status(thm)], ['9'])).
% 22.02/22.27  thf('11', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 22.02/22.27      inference('sup-', [status(thm)], ['8', '10'])).
% 22.02/22.27  thf(t1_xboole_0, axiom,
% 22.02/22.27    (![A:$i,B:$i,C:$i]:
% 22.02/22.27     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 22.02/22.27       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 22.02/22.27  thf('12', plain,
% 22.02/22.27      (![X9 : $i, X10 : $i, X12 : $i]:
% 22.02/22.27         ((r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X12))
% 22.02/22.27          | (r2_hidden @ X9 @ X12)
% 22.02/22.27          | ~ (r2_hidden @ X9 @ X10))),
% 22.02/22.27      inference('cnf', [status(esa)], [t1_xboole_0])).
% 22.02/22.27  thf('13', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         ((r2_hidden @ X0 @ X2)
% 22.02/22.27          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['11', '12'])).
% 22.02/22.27  thf(idempotence_k3_xboole_0, axiom,
% 22.02/22.27    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 22.02/22.27  thf('14', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 22.02/22.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 22.02/22.27  thf(t4_xboole_0, axiom,
% 22.02/22.27    (![A:$i,B:$i]:
% 22.02/22.27     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 22.02/22.27            ( r1_xboole_0 @ A @ B ) ) ) & 
% 22.02/22.27       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 22.02/22.27            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 22.02/22.27  thf('15', plain,
% 22.02/22.27      (![X13 : $i, X15 : $i, X16 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 22.02/22.27          | ~ (r1_xboole_0 @ X13 @ X16))),
% 22.02/22.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 22.02/22.27  thf('16', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 22.02/22.27      inference('sup-', [status(thm)], ['14', '15'])).
% 22.02/22.27  thf('17', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         ((r2_hidden @ X1 @ X0)
% 22.02/22.27          | ~ (r1_xboole_0 @ (k5_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) @ 
% 22.02/22.27               (k5_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['13', '16'])).
% 22.02/22.27  thf('18', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         (~ (r1_xboole_0 @ (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) @ 
% 22.02/22.27             (k5_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 22.02/22.27              (k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))
% 22.02/22.27          | (r2_hidden @ X1 @ (k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['4', '17'])).
% 22.02/22.27  thf('19', plain,
% 22.02/22.27      (![X23 : $i, X24 : $i]:
% 22.02/22.27         ((k4_xboole_0 @ X23 @ X24)
% 22.02/22.27           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 22.02/22.27      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.27  thf('20', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         (~ (r1_xboole_0 @ (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) @ 
% 22.02/22.27             (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))
% 22.02/22.27          | (r2_hidden @ X1 @ (k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 22.02/22.27      inference('demod', [status(thm)], ['18', '19'])).
% 22.02/22.27  thf('21', plain,
% 22.02/22.27      (((~ (r1_xboole_0 @ k1_xboole_0 @ 
% 22.02/22.27            (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 22.02/22.27         | (r2_hidden @ sk_B @ 
% 22.02/22.27            (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('sup-', [status(thm)], ['3', '20'])).
% 22.02/22.27  thf('22', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('split', [status(esa)], ['2'])).
% 22.02/22.27  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 22.02/22.27  thf('23', plain, (![X26 : $i]: (r1_xboole_0 @ X26 @ k1_xboole_0)),
% 22.02/22.27      inference('cnf', [status(esa)], [t65_xboole_1])).
% 22.02/22.27  thf('24', plain,
% 22.02/22.27      (![X13 : $i, X14 : $i]:
% 22.02/22.27         ((r1_xboole_0 @ X13 @ X14)
% 22.02/22.27          | (r2_hidden @ (sk_C @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 22.02/22.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 22.02/22.27  thf(commutativity_k3_xboole_0, axiom,
% 22.02/22.27    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 22.02/22.27  thf('25', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.02/22.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.02/22.27  thf('26', plain,
% 22.02/22.27      (![X13 : $i, X15 : $i, X16 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 22.02/22.27          | ~ (r1_xboole_0 @ X13 @ X16))),
% 22.02/22.27      inference('cnf', [status(esa)], [t4_xboole_0])).
% 22.02/22.27  thf('27', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 22.02/22.27          | ~ (r1_xboole_0 @ X0 @ X1))),
% 22.02/22.27      inference('sup-', [status(thm)], ['25', '26'])).
% 22.02/22.27  thf('28', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]:
% 22.02/22.27         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 22.02/22.27      inference('sup-', [status(thm)], ['24', '27'])).
% 22.02/22.27  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 22.02/22.27      inference('sup-', [status(thm)], ['23', '28'])).
% 22.02/22.27  thf('30', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.02/22.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.02/22.27  thf('31', plain,
% 22.02/22.27      (((r2_hidden @ sk_B @ (k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('demod', [status(thm)], ['21', '22', '29', '30'])).
% 22.02/22.27  thf('32', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.02/22.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.02/22.27  thf(d4_xboole_0, axiom,
% 22.02/22.27    (![A:$i,B:$i,C:$i]:
% 22.02/22.27     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 22.02/22.27       ( ![D:$i]:
% 22.02/22.27         ( ( r2_hidden @ D @ C ) <=>
% 22.02/22.27           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 22.02/22.27  thf('33', plain,
% 22.02/22.27      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X6 @ X5)
% 22.02/22.27          | (r2_hidden @ X6 @ X4)
% 22.02/22.27          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 22.02/22.27      inference('cnf', [status(esa)], [d4_xboole_0])).
% 22.02/22.27  thf('34', plain,
% 22.02/22.27      (![X3 : $i, X4 : $i, X6 : $i]:
% 22.02/22.27         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 22.02/22.27      inference('simplify', [status(thm)], ['33'])).
% 22.02/22.27  thf('35', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 22.02/22.27      inference('sup-', [status(thm)], ['32', '34'])).
% 22.02/22.27  thf('36', plain,
% 22.02/22.27      (((r2_hidden @ sk_B @ sk_C_1))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('sup-', [status(thm)], ['31', '35'])).
% 22.02/22.27  thf('37', plain,
% 22.02/22.27      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 22.02/22.27        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 22.02/22.27        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0)))),
% 22.02/22.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.27  thf('38', plain,
% 22.02/22.27      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 22.02/22.27      inference('split', [status(esa)], ['37'])).
% 22.02/22.27  thf('39', plain,
% 22.02/22.27      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 22.02/22.27       ((r2_hidden @ sk_B @ sk_C_1))),
% 22.02/22.27      inference('sup-', [status(thm)], ['36', '38'])).
% 22.02/22.27  thf('40', plain,
% 22.02/22.27      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 22.02/22.27       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 22.02/22.27       ~ ((r2_hidden @ sk_B @ sk_C_1))),
% 22.02/22.27      inference('split', [status(esa)], ['37'])).
% 22.02/22.27  thf('41', plain,
% 22.02/22.27      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 22.02/22.27      inference('split', [status(esa)], ['0'])).
% 22.02/22.27  thf('42', plain,
% 22.02/22.27      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 22.02/22.27      inference('split', [status(esa)], ['2'])).
% 22.02/22.27  thf(t53_zfmisc_1, axiom,
% 22.02/22.27    (![A:$i,B:$i,C:$i]:
% 22.02/22.27     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 22.02/22.27       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 22.02/22.27  thf('43', plain,
% 22.02/22.27      (![X59 : $i, X60 : $i, X61 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X59 @ X60)
% 22.02/22.27          | ~ (r2_hidden @ X61 @ X60)
% 22.02/22.27          | ((k3_xboole_0 @ (k2_tarski @ X59 @ X61) @ X60)
% 22.02/22.27              = (k2_tarski @ X59 @ X61)))),
% 22.02/22.27      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 22.02/22.27  thf('44', plain,
% 22.02/22.27      ((![X0 : $i]:
% 22.02/22.27          (((k3_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C_1)
% 22.02/22.27             = (k2_tarski @ sk_A @ X0))
% 22.02/22.27           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 22.02/22.27         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['42', '43'])).
% 22.02/22.27  thf('45', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.02/22.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.02/22.27  thf('46', plain,
% 22.02/22.27      ((![X0 : $i]:
% 22.02/22.27          (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ X0))
% 22.02/22.27             = (k2_tarski @ sk_A @ X0))
% 22.02/22.27           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 22.02/22.27         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 22.02/22.27      inference('demod', [status(thm)], ['44', '45'])).
% 22.02/22.27  thf('47', plain,
% 22.02/22.27      ((((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 22.02/22.27          = (k2_tarski @ sk_A @ sk_B)))
% 22.02/22.27         <= (((r2_hidden @ sk_A @ sk_C_1)) & ((r2_hidden @ sk_B @ sk_C_1)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['41', '46'])).
% 22.02/22.27  thf('48', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.02/22.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.02/22.27  thf('49', plain,
% 22.02/22.27      (![X23 : $i, X24 : $i]:
% 22.02/22.27         ((k4_xboole_0 @ X23 @ X24)
% 22.02/22.27           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 22.02/22.27      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.27  thf('50', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]:
% 22.02/22.27         ((k4_xboole_0 @ X0 @ X1)
% 22.02/22.27           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 22.02/22.27      inference('sup+', [status(thm)], ['48', '49'])).
% 22.02/22.27  thf('51', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27          = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 22.02/22.27             (k2_tarski @ sk_A @ sk_B))))
% 22.02/22.27         <= (((r2_hidden @ sk_A @ sk_C_1)) & ((r2_hidden @ sk_B @ sk_C_1)))),
% 22.02/22.27      inference('sup+', [status(thm)], ['47', '50'])).
% 22.02/22.27  thf(d10_xboole_0, axiom,
% 22.02/22.27    (![A:$i,B:$i]:
% 22.02/22.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 22.02/22.27  thf('52', plain,
% 22.02/22.27      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 22.02/22.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 22.02/22.27  thf('53', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 22.02/22.27      inference('simplify', [status(thm)], ['52'])).
% 22.02/22.27  thf(l32_xboole_1, axiom,
% 22.02/22.27    (![A:$i,B:$i]:
% 22.02/22.27     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 22.02/22.27  thf('54', plain,
% 22.02/22.27      (![X20 : $i, X22 : $i]:
% 22.02/22.27         (((k4_xboole_0 @ X20 @ X22) = (k1_xboole_0))
% 22.02/22.27          | ~ (r1_tarski @ X20 @ X22))),
% 22.02/22.27      inference('cnf', [status(esa)], [l32_xboole_1])).
% 22.02/22.27  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.02/22.27      inference('sup-', [status(thm)], ['53', '54'])).
% 22.02/22.27  thf('56', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 22.02/22.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 22.02/22.27  thf('57', plain,
% 22.02/22.27      (![X23 : $i, X24 : $i]:
% 22.02/22.27         ((k4_xboole_0 @ X23 @ X24)
% 22.02/22.27           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 22.02/22.27      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.27  thf('58', plain,
% 22.02/22.27      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 22.02/22.27      inference('sup+', [status(thm)], ['56', '57'])).
% 22.02/22.27  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.02/22.27      inference('demod', [status(thm)], ['55', '58'])).
% 22.02/22.27  thf('60', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 22.02/22.27         <= (((r2_hidden @ sk_A @ sk_C_1)) & ((r2_hidden @ sk_B @ sk_C_1)))),
% 22.02/22.27      inference('demod', [status(thm)], ['51', '59'])).
% 22.02/22.27  thf('61', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0)))
% 22.02/22.27         <= (~
% 22.02/22.27             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('split', [status(esa)], ['37'])).
% 22.02/22.27  thf('62', plain,
% 22.02/22.27      ((((k1_xboole_0) != (k1_xboole_0)))
% 22.02/22.27         <= (~
% 22.02/22.27             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))) & 
% 22.02/22.27             ((r2_hidden @ sk_A @ sk_C_1)) & 
% 22.02/22.27             ((r2_hidden @ sk_B @ sk_C_1)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['60', '61'])).
% 22.02/22.27  thf('63', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 22.02/22.27       ~ ((r2_hidden @ sk_A @ sk_C_1)) | ~ ((r2_hidden @ sk_B @ sk_C_1))),
% 22.02/22.27      inference('simplify', [status(thm)], ['62'])).
% 22.02/22.27  thf('64', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 22.02/22.27       ((r2_hidden @ sk_A @ sk_C_1))),
% 22.02/22.27      inference('split', [status(esa)], ['2'])).
% 22.02/22.27  thf('65', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('split', [status(esa)], ['2'])).
% 22.02/22.27  thf('66', plain,
% 22.02/22.27      (![X23 : $i, X24 : $i]:
% 22.02/22.27         ((k4_xboole_0 @ X23 @ X24)
% 22.02/22.27           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 22.02/22.27      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.27  thf('67', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 22.02/22.27          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 22.02/22.27      inference('sup+', [status(thm)], ['5', '7'])).
% 22.02/22.27  thf('68', plain,
% 22.02/22.27      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 22.02/22.27         (((X28) != (X27)) | ~ (zip_tseitin_0 @ X28 @ X29 @ X30 @ X27))),
% 22.02/22.27      inference('cnf', [status(esa)], [zf_stmt_2])).
% 22.02/22.27  thf('69', plain,
% 22.02/22.27      (![X27 : $i, X29 : $i, X30 : $i]:
% 22.02/22.27         ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X27)),
% 22.02/22.27      inference('simplify', [status(thm)], ['68'])).
% 22.02/22.27  thf('70', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 22.02/22.27      inference('sup-', [status(thm)], ['67', '69'])).
% 22.02/22.27  thf('71', plain,
% 22.02/22.27      (![X9 : $i, X10 : $i, X12 : $i]:
% 22.02/22.27         ((r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X12))
% 22.02/22.27          | (r2_hidden @ X9 @ X12)
% 22.02/22.27          | ~ (r2_hidden @ X9 @ X10))),
% 22.02/22.27      inference('cnf', [status(esa)], [t1_xboole_0])).
% 22.02/22.27  thf('72', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         ((r2_hidden @ X1 @ X2)
% 22.02/22.27          | (r2_hidden @ X1 @ (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['70', '71'])).
% 22.02/22.27  thf('73', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 22.02/22.27      inference('sup-', [status(thm)], ['14', '15'])).
% 22.02/22.27  thf('74', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         ((r2_hidden @ X2 @ X0)
% 22.02/22.27          | ~ (r1_xboole_0 @ (k5_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) @ 
% 22.02/22.27               (k5_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['72', '73'])).
% 22.02/22.27  thf('75', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         (~ (r1_xboole_0 @ (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) @ 
% 22.02/22.27             (k5_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 22.02/22.27              (k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))
% 22.02/22.27          | (r2_hidden @ X2 @ (k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 22.02/22.27      inference('sup-', [status(thm)], ['66', '74'])).
% 22.02/22.27  thf('76', plain,
% 22.02/22.27      (![X23 : $i, X24 : $i]:
% 22.02/22.27         ((k4_xboole_0 @ X23 @ X24)
% 22.02/22.27           = (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)))),
% 22.02/22.27      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.27  thf('77', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         (~ (r1_xboole_0 @ (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) @ 
% 22.02/22.27             (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))
% 22.02/22.27          | (r2_hidden @ X2 @ (k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 22.02/22.27      inference('demod', [status(thm)], ['75', '76'])).
% 22.02/22.27  thf('78', plain,
% 22.02/22.27      (((~ (r1_xboole_0 @ k1_xboole_0 @ 
% 22.02/22.27            (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 22.02/22.27         | (r2_hidden @ sk_A @ 
% 22.02/22.27            (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('sup-', [status(thm)], ['65', '77'])).
% 22.02/22.27  thf('79', plain,
% 22.02/22.27      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('split', [status(esa)], ['2'])).
% 22.02/22.27  thf('80', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 22.02/22.27      inference('sup-', [status(thm)], ['23', '28'])).
% 22.02/22.27  thf('81', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.02/22.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.02/22.27  thf('82', plain,
% 22.02/22.27      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 22.02/22.27  thf('83', plain,
% 22.02/22.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.27         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 22.02/22.27      inference('sup-', [status(thm)], ['32', '34'])).
% 22.02/22.27  thf('84', plain,
% 22.02/22.27      (((r2_hidden @ sk_A @ sk_C_1))
% 22.02/22.27         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 22.02/22.27                = (k1_xboole_0))))),
% 22.02/22.27      inference('sup-', [status(thm)], ['82', '83'])).
% 22.02/22.27  thf('85', plain,
% 22.02/22.27      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 22.02/22.27      inference('split', [status(esa)], ['37'])).
% 22.02/22.27  thf('86', plain,
% 22.02/22.27      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 22.02/22.27       ((r2_hidden @ sk_A @ sk_C_1))),
% 22.02/22.27      inference('sup-', [status(thm)], ['84', '85'])).
% 22.02/22.27  thf('87', plain, ($false),
% 22.02/22.27      inference('sat_resolution*', [status(thm)],
% 22.02/22.27                ['1', '39', '40', '63', '64', '86'])).
% 22.02/22.27  
% 22.02/22.27  % SZS output end Refutation
% 22.02/22.27  
% 22.12/22.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
