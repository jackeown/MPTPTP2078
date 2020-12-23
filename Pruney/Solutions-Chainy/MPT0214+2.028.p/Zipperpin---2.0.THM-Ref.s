%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.blmWBKCX1P

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:48 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 200 expanded)
%              Number of leaves         :   36 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  669 (1381 expanded)
%              Number of equality atoms :   75 ( 127 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36','39'])).

thf('41',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','40','41'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('43',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('45',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('48',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('49',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k2_tarski @ sk_B_1 @ sk_A )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X28 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X21 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X21 @ X22 @ X19 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('61',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ( X34 = X31 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('62',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34 = X31 )
      | ~ ( r2_hidden @ X34 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.blmWBKCX1P
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 579 iterations in 0.175s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.63  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.44/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(t6_zfmisc_1, conjecture,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.44/0.63       ( ( A ) = ( B ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i,B:$i]:
% 0.44/0.63        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.44/0.63          ( ( A ) = ( B ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.44/0.63  thf('0', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t28_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      (![X10 : $i, X11 : $i]:
% 0.44/0.63         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.44/0.63         = (k1_tarski @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.63  thf(t100_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.63  thf('3', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.63           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.63  thf('4', plain,
% 0.44/0.63      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.44/0.63         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.44/0.63  thf(t98_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.44/0.63  thf('5', plain,
% 0.44/0.63      (![X17 : $i, X18 : $i]:
% 0.44/0.63         ((k2_xboole_0 @ X17 @ X18)
% 0.44/0.63           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.63  thf('6', plain,
% 0.44/0.63      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.44/0.63         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ 
% 0.44/0.63            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.44/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.63  thf(t79_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.44/0.63      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.44/0.63  thf(symmetry_r1_xboole_0, axiom,
% 0.44/0.63    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.44/0.63  thf('8', plain,
% 0.44/0.63      (![X1 : $i, X2 : $i]:
% 0.44/0.63         ((r1_xboole_0 @ X1 @ X2) | ~ (r1_xboole_0 @ X2 @ X1))),
% 0.44/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.63  thf(t7_xboole_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.63          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.44/0.63  thf('10', plain,
% 0.44/0.63      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.44/0.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.63  thf(t4_xboole_0, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.63            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.63  thf('11', plain,
% 0.44/0.63      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.44/0.63          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.44/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.63  thf('12', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['9', '12'])).
% 0.44/0.63  thf(t48_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.63  thf('14', plain,
% 0.44/0.63      (![X12 : $i, X13 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.44/0.63           = (k3_xboole_0 @ X12 @ X13))),
% 0.44/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.63  thf('15', plain,
% 0.44/0.63      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.44/0.63      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.44/0.63  thf('16', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.44/0.63  thf('17', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.44/0.63          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['13', '16'])).
% 0.44/0.63  thf('18', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['9', '12'])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.63           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.44/0.63           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.63  thf(t5_boole, axiom,
% 0.44/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.63  thf('21', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.44/0.63  thf('22', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.44/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.44/0.63  thf('23', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.63      inference('demod', [status(thm)], ['17', '22'])).
% 0.44/0.63  thf('24', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.63  thf('25', plain,
% 0.44/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.63  thf('26', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.63           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.44/0.63           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.44/0.63  thf('28', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.44/0.63  thf('29', plain,
% 0.44/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.44/0.63  thf('30', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.44/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.44/0.63  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['29', '30'])).
% 0.44/0.63  thf('32', plain,
% 0.44/0.63      (![X12 : $i, X13 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.44/0.63           = (k3_xboole_0 @ X12 @ X13))),
% 0.44/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.63  thf('33', plain,
% 0.44/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['31', '32'])).
% 0.44/0.63  thf(idempotence_k3_xboole_0, axiom,
% 0.44/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.44/0.63  thf('34', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.63      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.44/0.63  thf('35', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ X8 @ X9)
% 0.44/0.63           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.63  thf('36', plain,
% 0.44/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['34', '35'])).
% 0.44/0.63  thf('37', plain,
% 0.44/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.44/0.63  thf('38', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['9', '12'])).
% 0.44/0.63  thf('39', plain,
% 0.44/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['37', '38'])).
% 0.44/0.63  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['33', '36', '39'])).
% 0.44/0.63  thf('41', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.44/0.63  thf('42', plain,
% 0.44/0.63      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.44/0.63         = (k1_tarski @ sk_B_1))),
% 0.44/0.63      inference('demod', [status(thm)], ['6', '40', '41'])).
% 0.44/0.63  thf(t69_enumset1, axiom,
% 0.44/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.63  thf('43', plain,
% 0.44/0.63      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.44/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.63  thf(t70_enumset1, axiom,
% 0.44/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      (![X41 : $i, X42 : $i]:
% 0.44/0.63         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.44/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.63  thf(t46_enumset1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.44/0.63       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.44/0.63  thf('45', plain,
% 0.44/0.63      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.44/0.63         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.44/0.63           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ (k1_tarski @ X39)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.44/0.63  thf('46', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.44/0.63           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['44', '45'])).
% 0.44/0.63  thf('47', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.44/0.63           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['43', '46'])).
% 0.44/0.63  thf(t71_enumset1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.44/0.63  thf('48', plain,
% 0.44/0.63      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.44/0.63         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.44/0.63           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.44/0.63      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.63  thf('49', plain,
% 0.44/0.63      (![X41 : $i, X42 : $i]:
% 0.44/0.63         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.44/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.63  thf('50', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['48', '49'])).
% 0.44/0.63  thf('51', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((k2_tarski @ X0 @ X1)
% 0.44/0.63           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.44/0.63      inference('demod', [status(thm)], ['47', '50'])).
% 0.44/0.63  thf('52', plain, (((k2_tarski @ sk_B_1 @ sk_A) = (k1_tarski @ sk_B_1))),
% 0.44/0.63      inference('demod', [status(thm)], ['42', '51'])).
% 0.44/0.63  thf('53', plain,
% 0.44/0.63      (![X41 : $i, X42 : $i]:
% 0.44/0.63         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.44/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.63  thf(d1_enumset1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.63       ( ![E:$i]:
% 0.44/0.63         ( ( r2_hidden @ E @ D ) <=>
% 0.44/0.63           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.44/0.63  thf(zf_stmt_2, axiom,
% 0.44/0.63    (![E:$i,C:$i,B:$i,A:$i]:
% 0.44/0.63     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.44/0.63       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_3, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.63       ( ![E:$i]:
% 0.44/0.63         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.44/0.63  thf('54', plain,
% 0.44/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.63         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.44/0.63          | (r2_hidden @ X24 @ X28)
% 0.44/0.63          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.63  thf('55', plain,
% 0.44/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.44/0.63         ((r2_hidden @ X24 @ (k1_enumset1 @ X27 @ X26 @ X25))
% 0.44/0.63          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27))),
% 0.44/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.44/0.63  thf('56', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.63          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.44/0.63      inference('sup+', [status(thm)], ['53', '55'])).
% 0.44/0.63  thf('57', plain,
% 0.44/0.63      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.63         (((X20) != (X21)) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.63  thf('58', plain,
% 0.44/0.63      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.44/0.63         ~ (zip_tseitin_0 @ X21 @ X21 @ X22 @ X19)),
% 0.44/0.63      inference('simplify', [status(thm)], ['57'])).
% 0.44/0.63  thf('59', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.44/0.63      inference('sup-', [status(thm)], ['56', '58'])).
% 0.44/0.63  thf('60', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.44/0.63      inference('sup+', [status(thm)], ['52', '59'])).
% 0.44/0.63  thf(d1_tarski, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.44/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.44/0.63  thf('61', plain,
% 0.44/0.63      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X34 @ X33)
% 0.44/0.63          | ((X34) = (X31))
% 0.44/0.63          | ((X33) != (k1_tarski @ X31)))),
% 0.44/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.63  thf('62', plain,
% 0.44/0.63      (![X31 : $i, X34 : $i]:
% 0.44/0.63         (((X34) = (X31)) | ~ (r2_hidden @ X34 @ (k1_tarski @ X31)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['61'])).
% 0.44/0.63  thf('63', plain, (((sk_A) = (sk_B_1))),
% 0.44/0.63      inference('sup-', [status(thm)], ['60', '62'])).
% 0.44/0.63  thf('64', plain, (((sk_A) != (sk_B_1))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('65', plain, ($false),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
