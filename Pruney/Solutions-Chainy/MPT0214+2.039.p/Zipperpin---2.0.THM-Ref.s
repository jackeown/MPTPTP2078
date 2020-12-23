%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iGEqnWqUSw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:49 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 149 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  776 (1109 expanded)
%              Number of equality atoms :   83 ( 128 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
       != ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','38','39'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('41',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('43',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('46',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('47',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k2_tarski @ sk_B_1 @ sk_A )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X22 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('60',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,
    ( ( sk_A = sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iGEqnWqUSw
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.79/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.03  % Solved by: fo/fo7.sh
% 0.79/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.03  % done 877 iterations in 0.524s
% 0.79/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.03  % SZS output start Refutation
% 0.79/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.03  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.79/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.79/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.79/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.79/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.79/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.79/1.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.79/1.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.79/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.79/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/1.03  thf(d1_enumset1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.79/1.03       ( ![E:$i]:
% 0.79/1.03         ( ( r2_hidden @ E @ D ) <=>
% 0.79/1.03           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.79/1.03  thf(zf_stmt_0, axiom,
% 0.79/1.03    (![E:$i,C:$i,B:$i,A:$i]:
% 0.79/1.03     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.79/1.03       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.79/1.03  thf('0', plain,
% 0.79/1.03      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.79/1.03         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.79/1.03          | ((X21) = (X22))
% 0.79/1.03          | ((X21) = (X23))
% 0.79/1.03          | ((X21) = (X24)))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.03  thf(t6_zfmisc_1, conjecture,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.79/1.03       ( ( A ) = ( B ) ) ))).
% 0.79/1.03  thf(zf_stmt_1, negated_conjecture,
% 0.79/1.03    (~( ![A:$i,B:$i]:
% 0.79/1.03        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.79/1.03          ( ( A ) = ( B ) ) ) )),
% 0.79/1.03    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.79/1.03  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.79/1.03  thf(t28_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/1.03  thf('2', plain,
% 0.79/1.03      (![X9 : $i, X10 : $i]:
% 0.79/1.03         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.79/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.79/1.03  thf('3', plain,
% 0.79/1.03      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.79/1.03         = (k1_tarski @ sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.79/1.03  thf(t100_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.79/1.03  thf('4', plain,
% 0.79/1.03      (![X7 : $i, X8 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X7 @ X8)
% 0.79/1.03           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/1.03  thf('5', plain,
% 0.79/1.03      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.79/1.03         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['3', '4'])).
% 0.79/1.03  thf(idempotence_k3_xboole_0, axiom,
% 0.79/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.79/1.03  thf('6', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.79/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.79/1.03  thf('7', plain,
% 0.79/1.03      (![X7 : $i, X8 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ X7 @ X8)
% 0.79/1.03           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/1.03  thf('8', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.79/1.03  thf('9', plain,
% 0.79/1.03      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.79/1.03         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.79/1.03      inference('demod', [status(thm)], ['5', '8'])).
% 0.79/1.03  thf(t98_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.79/1.03  thf('10', plain,
% 0.79/1.03      (![X18 : $i, X19 : $i]:
% 0.79/1.03         ((k2_xboole_0 @ X18 @ X19)
% 0.79/1.03           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.79/1.03  thf('11', plain,
% 0.79/1.03      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.79/1.03         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ 
% 0.79/1.03            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.79/1.03      inference('sup+', [status(thm)], ['9', '10'])).
% 0.79/1.03  thf('12', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.79/1.03  thf(t91_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.79/1.03       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.79/1.03  thf('13', plain,
% 0.79/1.03      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/1.03         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.79/1.03           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.79/1.03  thf('14', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.79/1.03           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['12', '13'])).
% 0.79/1.03  thf('15', plain,
% 0.79/1.03      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/1.03         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.79/1.03           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.79/1.03  thf('16', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.79/1.03  thf('17', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.79/1.03           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.79/1.03      inference('sup+', [status(thm)], ['15', '16'])).
% 0.79/1.03  thf('18', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))
% 0.79/1.03           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['14', '17'])).
% 0.79/1.03  thf('19', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.79/1.03  thf('20', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.79/1.03  thf('21', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.79/1.03  thf('22', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.79/1.03           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['12', '13'])).
% 0.79/1.03  thf('23', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.03         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.79/1.03           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['21', '22'])).
% 0.79/1.03  thf('24', plain,
% 0.79/1.03      (![X18 : $i, X19 : $i]:
% 0.79/1.03         ((k2_xboole_0 @ X18 @ X19)
% 0.79/1.03           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.79/1.03  thf(idempotence_k2_xboole_0, axiom,
% 0.79/1.03    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.79/1.03  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.79/1.03      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.79/1.03  thf('26', plain,
% 0.79/1.03      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.79/1.03      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.79/1.03  thf('27', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0))
% 0.79/1.03           = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('demod', [status(thm)], ['18', '19', '20', '26'])).
% 0.79/1.03  thf('28', plain,
% 0.79/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.79/1.03  thf('29', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.03         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0))
% 0.79/1.03           = (k4_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('demod', [status(thm)], ['27', '28'])).
% 0.79/1.03  thf(t83_xboole_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/1.03  thf('30', plain,
% 0.79/1.03      (![X12 : $i, X14 : $i]:
% 0.79/1.03         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.79/1.03  thf('31', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.03         (((k4_xboole_0 @ X0 @ X0) != (k4_xboole_0 @ X0 @ X0))
% 0.79/1.03          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['29', '30'])).
% 0.79/1.03  thf('32', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.03         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('simplify', [status(thm)], ['31'])).
% 0.79/1.03  thf(t7_xboole_0, axiom,
% 0.79/1.03    (![A:$i]:
% 0.79/1.03     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.79/1.03          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.79/1.03  thf('33', plain,
% 0.79/1.03      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.79/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.79/1.03  thf('34', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.79/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.79/1.03  thf(t4_xboole_0, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.79/1.03            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.79/1.03       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.79/1.03            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.79/1.03  thf('35', plain,
% 0.79/1.03      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.79/1.03          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.79/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.79/1.03  thf('36', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['34', '35'])).
% 0.79/1.03  thf('37', plain,
% 0.79/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['33', '36'])).
% 0.79/1.03  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['32', '37'])).
% 0.79/1.03  thf(t5_boole, axiom,
% 0.79/1.03    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/1.03  thf('39', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.79/1.03      inference('cnf', [status(esa)], [t5_boole])).
% 0.79/1.03  thf('40', plain,
% 0.79/1.03      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.79/1.03         = (k1_tarski @ sk_B_1))),
% 0.79/1.03      inference('demod', [status(thm)], ['11', '38', '39'])).
% 0.79/1.03  thf(t69_enumset1, axiom,
% 0.79/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.79/1.03  thf('41', plain,
% 0.79/1.03      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.79/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.79/1.03  thf(t70_enumset1, axiom,
% 0.79/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.79/1.03  thf('42', plain,
% 0.79/1.03      (![X41 : $i, X42 : $i]:
% 0.79/1.03         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.79/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.79/1.03  thf(t46_enumset1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.03     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.79/1.03       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.79/1.03  thf('43', plain,
% 0.79/1.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.79/1.03         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.79/1.03           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ (k1_tarski @ X39)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.79/1.03  thf('44', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.79/1.03           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['42', '43'])).
% 0.79/1.03  thf('45', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.79/1.03           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['41', '44'])).
% 0.79/1.03  thf(t71_enumset1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.79/1.03  thf('46', plain,
% 0.79/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.79/1.03         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.79/1.03           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.79/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.79/1.03  thf('47', plain,
% 0.79/1.03      (![X41 : $i, X42 : $i]:
% 0.79/1.03         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.79/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.79/1.03  thf('48', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['46', '47'])).
% 0.79/1.03  thf('49', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((k2_tarski @ X0 @ X1)
% 0.79/1.03           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.79/1.03      inference('demod', [status(thm)], ['45', '48'])).
% 0.79/1.03  thf('50', plain, (((k2_tarski @ sk_B_1 @ sk_A) = (k1_tarski @ sk_B_1))),
% 0.79/1.03      inference('demod', [status(thm)], ['40', '49'])).
% 0.79/1.03  thf('51', plain,
% 0.79/1.03      (![X41 : $i, X42 : $i]:
% 0.79/1.03         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.79/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.79/1.03  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.79/1.03  thf(zf_stmt_3, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.79/1.03       ( ![E:$i]:
% 0.79/1.03         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.79/1.03  thf('52', plain,
% 0.79/1.03      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.79/1.03         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.79/1.03          | (r2_hidden @ X25 @ X29)
% 0.79/1.03          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.79/1.03  thf('53', plain,
% 0.79/1.03      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.79/1.03         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 0.79/1.03          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 0.79/1.03      inference('simplify', [status(thm)], ['52'])).
% 0.79/1.03  thf('54', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.79/1.03          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.79/1.03      inference('sup+', [status(thm)], ['51', '53'])).
% 0.79/1.03  thf('55', plain,
% 0.79/1.03      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.79/1.03         (((X21) != (X22)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.03  thf('56', plain,
% 0.79/1.03      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.79/1.03         ~ (zip_tseitin_0 @ X22 @ X22 @ X23 @ X20)),
% 0.79/1.03      inference('simplify', [status(thm)], ['55'])).
% 0.79/1.03  thf('57', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['54', '56'])).
% 0.79/1.03  thf('58', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.79/1.03      inference('sup+', [status(thm)], ['50', '57'])).
% 0.79/1.03  thf('59', plain,
% 0.79/1.03      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.79/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.79/1.03  thf('60', plain,
% 0.79/1.03      (![X41 : $i, X42 : $i]:
% 0.79/1.03         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.79/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.79/1.03  thf('61', plain,
% 0.79/1.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X30 @ X29)
% 0.79/1.03          | ~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 0.79/1.03          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.79/1.03  thf('62', plain,
% 0.79/1.03      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.79/1.03         (~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 0.79/1.03          | ~ (r2_hidden @ X30 @ (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.79/1.03      inference('simplify', [status(thm)], ['61'])).
% 0.79/1.03  thf('63', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.79/1.03          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['60', '62'])).
% 0.79/1.03  thf('64', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.79/1.03          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['59', '63'])).
% 0.79/1.03  thf('65', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['58', '64'])).
% 0.79/1.03  thf('66', plain,
% 0.79/1.03      ((((sk_A) = (sk_B_1)) | ((sk_A) = (sk_B_1)) | ((sk_A) = (sk_B_1)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['0', '65'])).
% 0.79/1.03  thf('67', plain, (((sk_A) = (sk_B_1))),
% 0.79/1.03      inference('simplify', [status(thm)], ['66'])).
% 0.79/1.03  thf('68', plain, (((sk_A) != (sk_B_1))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.79/1.03  thf('69', plain, ($false),
% 0.79/1.03      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.79/1.03  
% 0.79/1.03  % SZS output end Refutation
% 0.79/1.03  
% 0.87/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
