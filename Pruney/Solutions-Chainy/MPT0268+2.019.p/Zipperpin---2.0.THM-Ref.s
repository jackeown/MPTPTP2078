%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sI8K2vkrz5

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:54 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 146 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  756 (1096 expanded)
%              Number of equality atoms :   76 ( 114 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
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
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('12',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X42 ) @ X43 )
      | ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','44','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('71',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','37','38','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sI8K2vkrz5
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.78/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/1.01  % Solved by: fo/fo7.sh
% 0.78/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/1.01  % done 1103 iterations in 0.552s
% 0.78/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/1.01  % SZS output start Refutation
% 0.78/1.01  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.78/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/1.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.78/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/1.01  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.78/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.78/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.78/1.01  thf(t65_zfmisc_1, conjecture,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.78/1.01       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.78/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.78/1.01    (~( ![A:$i,B:$i]:
% 0.78/1.01        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.78/1.01          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.78/1.01    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.78/1.01  thf('0', plain,
% 0.78/1.01      (((r2_hidden @ sk_B @ sk_A)
% 0.78/1.01        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('1', plain,
% 0.78/1.01      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.78/1.01       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.78/1.01      inference('split', [status(esa)], ['0'])).
% 0.78/1.01  thf('2', plain,
% 0.78/1.01      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.78/1.01      inference('split', [status(esa)], ['0'])).
% 0.78/1.01  thf(t70_enumset1, axiom,
% 0.78/1.01    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.78/1.01  thf('3', plain,
% 0.78/1.01      (![X33 : $i, X34 : $i]:
% 0.78/1.01         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.78/1.01      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.78/1.01  thf(d1_enumset1, axiom,
% 0.78/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/1.01     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.78/1.01       ( ![E:$i]:
% 0.78/1.01         ( ( r2_hidden @ E @ D ) <=>
% 0.78/1.01           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.78/1.01  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.78/1.01  thf(zf_stmt_2, axiom,
% 0.78/1.01    (![E:$i,C:$i,B:$i,A:$i]:
% 0.78/1.01     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.78/1.01       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.78/1.01  thf(zf_stmt_3, axiom,
% 0.78/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/1.01     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.78/1.01       ( ![E:$i]:
% 0.78/1.01         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.78/1.01  thf('4', plain,
% 0.78/1.01      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.78/1.01         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.78/1.01          | (r2_hidden @ X25 @ X29)
% 0.78/1.01          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.78/1.01  thf('5', plain,
% 0.78/1.01      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.78/1.01         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 0.78/1.01          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 0.78/1.01      inference('simplify', [status(thm)], ['4'])).
% 0.78/1.01  thf('6', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.01         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.78/1.01          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.78/1.01      inference('sup+', [status(thm)], ['3', '5'])).
% 0.78/1.01  thf('7', plain,
% 0.78/1.01      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.78/1.01         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.78/1.01  thf('8', plain,
% 0.78/1.01      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.78/1.01         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 0.78/1.01      inference('simplify', [status(thm)], ['7'])).
% 0.78/1.01  thf('9', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.78/1.01      inference('sup-', [status(thm)], ['6', '8'])).
% 0.78/1.01  thf(t69_enumset1, axiom,
% 0.78/1.01    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.78/1.01  thf('10', plain,
% 0.78/1.01      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.78/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.78/1.01  thf(idempotence_k3_xboole_0, axiom,
% 0.78/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/1.01  thf('11', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.78/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/1.01  thf(l27_zfmisc_1, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.78/1.01  thf('12', plain,
% 0.78/1.01      (![X42 : $i, X43 : $i]:
% 0.78/1.01         ((r1_xboole_0 @ (k1_tarski @ X42) @ X43) | (r2_hidden @ X42 @ X43))),
% 0.78/1.01      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.78/1.01  thf(t83_xboole_1, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.78/1.01  thf('13', plain,
% 0.78/1.01      (![X17 : $i, X18 : $i]:
% 0.78/1.01         (((k4_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_xboole_0 @ X17 @ X18))),
% 0.78/1.01      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.78/1.01  thf('14', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         ((r2_hidden @ X1 @ X0)
% 0.78/1.01          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['12', '13'])).
% 0.78/1.01  thf(t48_xboole_1, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.78/1.01  thf('15', plain,
% 0.78/1.01      (![X14 : $i, X15 : $i]:
% 0.78/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.78/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.78/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/1.01  thf('16', plain,
% 0.78/1.01      (![X14 : $i, X15 : $i]:
% 0.78/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.78/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.78/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/1.01  thf('17', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.78/1.01           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.78/1.01      inference('sup+', [status(thm)], ['15', '16'])).
% 0.78/1.01  thf(d5_xboole_0, axiom,
% 0.78/1.01    (![A:$i,B:$i,C:$i]:
% 0.78/1.01     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.78/1.01       ( ![D:$i]:
% 0.78/1.01         ( ( r2_hidden @ D @ C ) <=>
% 0.78/1.01           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.78/1.01  thf('18', plain,
% 0.78/1.01      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X6 @ X5)
% 0.78/1.01          | ~ (r2_hidden @ X6 @ X4)
% 0.78/1.01          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.78/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.78/1.01  thf('19', plain,
% 0.78/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X6 @ X4)
% 0.78/1.01          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.78/1.01      inference('simplify', [status(thm)], ['18'])).
% 0.78/1.01  thf('20', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.78/1.01          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['17', '19'])).
% 0.78/1.01  thf('21', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X2 @ 
% 0.78/1.01             (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.78/1.01          | (r2_hidden @ X0 @ X1)
% 0.78/1.01          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['14', '20'])).
% 0.78/1.01  thf('22', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.78/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/1.01  thf('23', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.78/1.01          | (r2_hidden @ X0 @ X1)
% 0.78/1.01          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.78/1.01      inference('demod', [status(thm)], ['21', '22'])).
% 0.78/1.01  thf('24', plain,
% 0.78/1.01      (![X14 : $i, X15 : $i]:
% 0.78/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.78/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.78/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/1.01  thf('25', plain,
% 0.78/1.01      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X6 @ X5)
% 0.78/1.01          | (r2_hidden @ X6 @ X3)
% 0.78/1.01          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.78/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.78/1.01  thf('26', plain,
% 0.78/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.78/1.01         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.78/1.01      inference('simplify', [status(thm)], ['25'])).
% 0.78/1.01  thf('27', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.78/1.01      inference('sup-', [status(thm)], ['24', '26'])).
% 0.78/1.01  thf('28', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.78/1.01          | (r2_hidden @ X0 @ X1))),
% 0.78/1.01      inference('clc', [status(thm)], ['23', '27'])).
% 0.78/1.01  thf('29', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.78/1.01          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['11', '28'])).
% 0.78/1.01  thf('30', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.78/1.01          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['10', '29'])).
% 0.78/1.01  thf('31', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.78/1.01      inference('sup-', [status(thm)], ['9', '30'])).
% 0.78/1.01  thf('32', plain,
% 0.78/1.01      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.78/1.01        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.78/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.01  thf('33', plain,
% 0.78/1.01      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.78/1.01         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.78/1.01      inference('split', [status(esa)], ['32'])).
% 0.78/1.01  thf('34', plain,
% 0.78/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.78/1.01         (~ (r2_hidden @ X6 @ X4)
% 0.78/1.01          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.78/1.01      inference('simplify', [status(thm)], ['18'])).
% 0.78/1.01  thf('35', plain,
% 0.78/1.01      ((![X0 : $i]:
% 0.78/1.01          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.78/1.01         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['33', '34'])).
% 0.78/1.01  thf('36', plain,
% 0.78/1.01      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.78/1.01         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.78/1.01      inference('sup-', [status(thm)], ['31', '35'])).
% 0.78/1.01  thf('37', plain,
% 0.78/1.01      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.78/1.01       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['2', '36'])).
% 0.78/1.01  thf('38', plain,
% 0.78/1.01      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.78/1.01       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.78/1.01      inference('split', [status(esa)], ['32'])).
% 0.78/1.01  thf('39', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         ((r2_hidden @ X1 @ X0)
% 0.78/1.01          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.78/1.01      inference('sup-', [status(thm)], ['12', '13'])).
% 0.78/1.01  thf('40', plain,
% 0.78/1.01      (![X14 : $i, X15 : $i]:
% 0.78/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.78/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.78/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/1.01  thf('41', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]:
% 0.78/1.01         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.78/1.01            = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.78/1.01          | (r2_hidden @ X0 @ X1))),
% 0.78/1.01      inference('sup+', [status(thm)], ['39', '40'])).
% 0.78/1.01  thf('42', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.78/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/1.01  thf(t100_xboole_1, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/1.01  thf('43', plain,
% 0.78/1.01      (![X9 : $i, X10 : $i]:
% 0.78/1.01         ((k4_xboole_0 @ X9 @ X10)
% 0.78/1.01           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.78/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/1.01  thf('44', plain,
% 0.78/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/1.01      inference('sup+', [status(thm)], ['42', '43'])).
% 0.78/1.01  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.78/1.01  thf('45', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.78/1.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.78/1.01  thf(t28_xboole_1, axiom,
% 0.78/1.01    (![A:$i,B:$i]:
% 0.78/1.01     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.78/1.01  thf('46', plain,
% 0.78/1.01      (![X11 : $i, X12 : $i]:
% 0.78/1.01         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.78/1.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/1.01  thf('47', plain,
% 0.78/1.01      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.78/1.01      inference('sup-', [status(thm)], ['45', '46'])).
% 0.78/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.78/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.78/1.01  thf('48', plain,
% 0.78/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.01  thf('49', plain,
% 0.84/1.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.01      inference('sup+', [status(thm)], ['47', '48'])).
% 0.84/1.01  thf('50', plain,
% 0.84/1.01      (![X9 : $i, X10 : $i]:
% 0.84/1.01         ((k4_xboole_0 @ X9 @ X10)
% 0.84/1.01           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.84/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.01  thf('51', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.01      inference('sup+', [status(thm)], ['49', '50'])).
% 0.84/1.01  thf(t5_boole, axiom,
% 0.84/1.01    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.84/1.01  thf('52', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.84/1.01      inference('cnf', [status(esa)], [t5_boole])).
% 0.84/1.01  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.84/1.01      inference('demod', [status(thm)], ['51', '52'])).
% 0.84/1.01  thf('54', plain,
% 0.84/1.01      (![X14 : $i, X15 : $i]:
% 0.84/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.84/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.84/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.84/1.01  thf('55', plain,
% 0.84/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.01      inference('sup+', [status(thm)], ['53', '54'])).
% 0.84/1.01  thf('56', plain,
% 0.84/1.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.01      inference('sup+', [status(thm)], ['47', '48'])).
% 0.84/1.01  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.01      inference('demod', [status(thm)], ['55', '56'])).
% 0.84/1.01  thf('58', plain,
% 0.84/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.84/1.01      inference('sup+', [status(thm)], ['42', '43'])).
% 0.84/1.01  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.01      inference('demod', [status(thm)], ['57', '58'])).
% 0.84/1.01  thf('60', plain,
% 0.84/1.01      (![X0 : $i, X1 : $i]:
% 0.84/1.01         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.84/1.01          | (r2_hidden @ X0 @ X1))),
% 0.84/1.01      inference('demod', [status(thm)], ['41', '44', '59'])).
% 0.84/1.01  thf('61', plain,
% 0.84/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.01  thf('62', plain,
% 0.84/1.01      (![X9 : $i, X10 : $i]:
% 0.84/1.01         ((k4_xboole_0 @ X9 @ X10)
% 0.84/1.01           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.84/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.01  thf('63', plain,
% 0.84/1.01      (![X0 : $i, X1 : $i]:
% 0.84/1.01         ((k4_xboole_0 @ X0 @ X1)
% 0.84/1.01           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.84/1.01      inference('sup+', [status(thm)], ['61', '62'])).
% 0.84/1.01  thf('64', plain,
% 0.84/1.01      (![X0 : $i, X1 : $i]:
% 0.84/1.01         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.84/1.01            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.01          | (r2_hidden @ X1 @ X0))),
% 0.84/1.01      inference('sup+', [status(thm)], ['60', '63'])).
% 0.84/1.01  thf('65', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.84/1.01      inference('cnf', [status(esa)], [t5_boole])).
% 0.84/1.01  thf('66', plain,
% 0.84/1.01      (![X0 : $i, X1 : $i]:
% 0.84/1.01         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.84/1.01          | (r2_hidden @ X1 @ X0))),
% 0.84/1.01      inference('demod', [status(thm)], ['64', '65'])).
% 0.84/1.01  thf('67', plain,
% 0.84/1.01      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.84/1.01         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.84/1.01      inference('split', [status(esa)], ['0'])).
% 0.84/1.01  thf('68', plain,
% 0.84/1.01      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.84/1.01         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.84/1.01      inference('sup-', [status(thm)], ['66', '67'])).
% 0.84/1.01  thf('69', plain,
% 0.84/1.01      (((r2_hidden @ sk_B @ sk_A))
% 0.84/1.01         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.84/1.01      inference('simplify', [status(thm)], ['68'])).
% 0.84/1.01  thf('70', plain,
% 0.84/1.01      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.84/1.01      inference('split', [status(esa)], ['32'])).
% 0.84/1.01  thf('71', plain,
% 0.84/1.01      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.84/1.01       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.84/1.01      inference('sup-', [status(thm)], ['69', '70'])).
% 0.84/1.01  thf('72', plain, ($false),
% 0.84/1.01      inference('sat_resolution*', [status(thm)], ['1', '37', '38', '71'])).
% 0.84/1.01  
% 0.84/1.01  % SZS output end Refutation
% 0.84/1.01  
% 0.84/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
