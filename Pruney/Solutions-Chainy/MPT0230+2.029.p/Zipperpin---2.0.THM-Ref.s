%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IYk9UZzUsJ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:14 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 227 expanded)
%              Number of leaves         :   38 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  773 (1763 expanded)
%              Number of equality atoms :   92 ( 213 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X45: $i] :
      ( ( k2_tarski @ X45 @ X45 )
      = ( k1_tarski @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k2_tarski @ X33 @ X34 ) @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('33',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_C @ X0 @ X0 )
      = ( k3_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('38',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('43',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('44',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ X0 )
      = ( k1_enumset1 @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_B @ sk_C @ X0 @ X0 )
      = ( k1_enumset1 @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['36','47'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('49',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( k1_enumset1 @ X73 @ X75 @ X74 )
      = ( k1_enumset1 @ X73 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('50',plain,
    ( ( k1_enumset1 @ sk_B @ sk_A @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['31','48','49'])).

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

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('54',plain,(
    ! [X27: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X29 )
      | ( X31 = X30 )
      | ( X31 = X27 )
      | ( X29
       != ( k2_tarski @ X30 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('55',plain,(
    ! [X27: $i,X30: $i,X31: $i] :
      ( ( X31 = X27 )
      | ( X31 = X30 )
      | ~ ( r2_hidden @ X31 @ ( k2_tarski @ X30 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X18 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IYk9UZzUsJ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.13/2.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.13/2.36  % Solved by: fo/fo7.sh
% 2.13/2.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.36  % done 3120 iterations in 1.910s
% 2.13/2.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.13/2.36  % SZS output start Refutation
% 2.13/2.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.13/2.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.13/2.36  thf(sk_B_type, type, sk_B: $i).
% 2.13/2.36  thf(sk_C_type, type, sk_C: $i).
% 2.13/2.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.13/2.36  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.13/2.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.13/2.36  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.13/2.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.13/2.36  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.13/2.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.13/2.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.13/2.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.13/2.36  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.13/2.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.13/2.36  thf(t25_zfmisc_1, conjecture,
% 2.13/2.36    (![A:$i,B:$i,C:$i]:
% 2.13/2.36     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 2.13/2.36          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 2.13/2.36  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.36    (~( ![A:$i,B:$i,C:$i]:
% 2.13/2.36        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 2.13/2.36             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 2.13/2.36    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 2.13/2.36  thf('0', plain,
% 2.13/2.36      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 2.13/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.36  thf(t28_xboole_1, axiom,
% 2.13/2.36    (![A:$i,B:$i]:
% 2.13/2.36     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.13/2.36  thf('1', plain,
% 2.13/2.36      (![X7 : $i, X8 : $i]:
% 2.13/2.36         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 2.13/2.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.13/2.36  thf('2', plain,
% 2.13/2.36      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 2.13/2.36         = (k1_tarski @ sk_A))),
% 2.13/2.36      inference('sup-', [status(thm)], ['0', '1'])).
% 2.13/2.36  thf(t100_xboole_1, axiom,
% 2.13/2.36    (![A:$i,B:$i]:
% 2.13/2.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.13/2.36  thf('3', plain,
% 2.13/2.36      (![X3 : $i, X4 : $i]:
% 2.13/2.36         ((k4_xboole_0 @ X3 @ X4)
% 2.13/2.36           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.13/2.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.13/2.36  thf('4', plain,
% 2.13/2.36      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 2.13/2.36         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 2.13/2.36      inference('sup+', [status(thm)], ['2', '3'])).
% 2.13/2.36  thf(t17_xboole_1, axiom,
% 2.13/2.36    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.13/2.36  thf('5', plain,
% 2.13/2.36      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 2.13/2.36      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.13/2.36  thf(t3_xboole_1, axiom,
% 2.13/2.36    (![A:$i]:
% 2.13/2.36     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.13/2.36  thf('6', plain,
% 2.13/2.36      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 2.13/2.36      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.13/2.36  thf('7', plain,
% 2.13/2.36      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.13/2.36      inference('sup-', [status(thm)], ['5', '6'])).
% 2.13/2.36  thf(commutativity_k3_xboole_0, axiom,
% 2.13/2.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.13/2.36  thf('8', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.13/2.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.36  thf('9', plain,
% 2.13/2.36      (![X3 : $i, X4 : $i]:
% 2.13/2.36         ((k4_xboole_0 @ X3 @ X4)
% 2.13/2.36           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.13/2.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.13/2.36  thf('10', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i]:
% 2.13/2.36         ((k4_xboole_0 @ X0 @ X1)
% 2.13/2.36           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.13/2.36      inference('sup+', [status(thm)], ['8', '9'])).
% 2.13/2.36  thf('11', plain,
% 2.13/2.36      (![X0 : $i]:
% 2.13/2.36         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['7', '10'])).
% 2.13/2.36  thf(t5_boole, axiom,
% 2.13/2.36    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.13/2.36  thf('12', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.13/2.36      inference('cnf', [status(esa)], [t5_boole])).
% 2.13/2.36  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.13/2.36      inference('demod', [status(thm)], ['11', '12'])).
% 2.13/2.36  thf(t48_xboole_1, axiom,
% 2.13/2.36    (![A:$i,B:$i]:
% 2.13/2.36     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.13/2.36  thf('14', plain,
% 2.13/2.36      (![X10 : $i, X11 : $i]:
% 2.13/2.36         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 2.13/2.36           = (k3_xboole_0 @ X10 @ X11))),
% 2.13/2.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.13/2.36  thf('15', plain,
% 2.13/2.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['13', '14'])).
% 2.13/2.36  thf(idempotence_k3_xboole_0, axiom,
% 2.13/2.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 2.13/2.36  thf('16', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 2.13/2.36      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.13/2.36  thf('17', plain,
% 2.13/2.36      (![X3 : $i, X4 : $i]:
% 2.13/2.36         ((k4_xboole_0 @ X3 @ X4)
% 2.13/2.36           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.13/2.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.13/2.36  thf('18', plain,
% 2.13/2.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['16', '17'])).
% 2.13/2.36  thf('19', plain,
% 2.13/2.36      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.13/2.36      inference('sup-', [status(thm)], ['5', '6'])).
% 2.13/2.36  thf('20', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.13/2.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.13/2.36  thf('21', plain,
% 2.13/2.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['19', '20'])).
% 2.13/2.36  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.13/2.36      inference('demod', [status(thm)], ['15', '18', '21'])).
% 2.13/2.36  thf('23', plain,
% 2.13/2.36      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 2.13/2.36         = (k1_xboole_0))),
% 2.13/2.36      inference('demod', [status(thm)], ['4', '22'])).
% 2.13/2.36  thf(t98_xboole_1, axiom,
% 2.13/2.36    (![A:$i,B:$i]:
% 2.13/2.36     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.13/2.36  thf('24', plain,
% 2.13/2.36      (![X13 : $i, X14 : $i]:
% 2.13/2.36         ((k2_xboole_0 @ X13 @ X14)
% 2.13/2.36           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 2.13/2.36      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.13/2.36  thf('25', plain,
% 2.13/2.36      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 2.13/2.36         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['23', '24'])).
% 2.13/2.36  thf('26', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.13/2.36      inference('cnf', [status(esa)], [t5_boole])).
% 2.13/2.36  thf('27', plain,
% 2.13/2.36      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 2.13/2.36         = (k2_tarski @ sk_B @ sk_C))),
% 2.13/2.36      inference('demod', [status(thm)], ['25', '26'])).
% 2.13/2.36  thf(t69_enumset1, axiom,
% 2.13/2.36    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.13/2.36  thf('28', plain,
% 2.13/2.36      (![X45 : $i]: ((k2_tarski @ X45 @ X45) = (k1_tarski @ X45))),
% 2.13/2.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.13/2.36  thf(l53_enumset1, axiom,
% 2.13/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.36     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 2.13/2.36       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 2.13/2.36  thf('29', plain,
% 2.13/2.36      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.13/2.36         ((k2_enumset1 @ X33 @ X34 @ X35 @ X36)
% 2.13/2.36           = (k2_xboole_0 @ (k2_tarski @ X33 @ X34) @ (k2_tarski @ X35 @ X36)))),
% 2.13/2.36      inference('cnf', [status(esa)], [l53_enumset1])).
% 2.13/2.36  thf('30', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.36         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 2.13/2.36           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 2.13/2.36      inference('sup+', [status(thm)], ['28', '29'])).
% 2.13/2.36  thf('31', plain,
% 2.13/2.36      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 2.13/2.36      inference('demod', [status(thm)], ['27', '30'])).
% 2.13/2.36  thf('32', plain,
% 2.13/2.36      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 2.13/2.36      inference('demod', [status(thm)], ['27', '30'])).
% 2.13/2.36  thf(t50_enumset1, axiom,
% 2.13/2.36    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.13/2.36     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 2.13/2.36       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 2.13/2.36  thf('33', plain,
% 2.13/2.36      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.13/2.36         ((k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44)
% 2.13/2.36           = (k2_xboole_0 @ (k2_enumset1 @ X40 @ X41 @ X42 @ X43) @ 
% 2.13/2.36              (k1_tarski @ X44)))),
% 2.13/2.36      inference('cnf', [status(esa)], [t50_enumset1])).
% 2.13/2.36  thf('34', plain,
% 2.13/2.36      (![X0 : $i]:
% 2.13/2.36         ((k3_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ X0)
% 2.13/2.36           = (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ X0)))),
% 2.13/2.36      inference('sup+', [status(thm)], ['32', '33'])).
% 2.13/2.36  thf('35', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.36         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 2.13/2.36           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 2.13/2.36      inference('sup+', [status(thm)], ['28', '29'])).
% 2.13/2.36  thf('36', plain,
% 2.13/2.36      (![X0 : $i]:
% 2.13/2.36         ((k2_enumset1 @ sk_B @ sk_C @ X0 @ X0)
% 2.13/2.36           = (k3_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ X0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['34', '35'])).
% 2.13/2.36  thf('37', plain,
% 2.13/2.36      (![X0 : $i]:
% 2.13/2.36         ((k3_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ X0)
% 2.13/2.36           = (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ X0)))),
% 2.13/2.36      inference('sup+', [status(thm)], ['32', '33'])).
% 2.13/2.36  thf(t71_enumset1, axiom,
% 2.13/2.36    (![A:$i,B:$i,C:$i]:
% 2.13/2.36     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.13/2.36  thf('38', plain,
% 2.13/2.36      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.13/2.36         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 2.13/2.36           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 2.13/2.36      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.13/2.36  thf(t70_enumset1, axiom,
% 2.13/2.36    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.13/2.36  thf('39', plain,
% 2.13/2.36      (![X46 : $i, X47 : $i]:
% 2.13/2.36         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 2.13/2.36      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.13/2.36  thf('40', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i]:
% 2.13/2.36         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['38', '39'])).
% 2.13/2.36  thf('41', plain,
% 2.13/2.36      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.13/2.36         ((k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44)
% 2.13/2.36           = (k2_xboole_0 @ (k2_enumset1 @ X40 @ X41 @ X42 @ X43) @ 
% 2.13/2.36              (k1_tarski @ X44)))),
% 2.13/2.36      inference('cnf', [status(esa)], [t50_enumset1])).
% 2.13/2.36  thf('42', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.36         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 2.13/2.36           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 2.13/2.36      inference('sup+', [status(thm)], ['40', '41'])).
% 2.13/2.36  thf(t72_enumset1, axiom,
% 2.13/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.36     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.13/2.36  thf('43', plain,
% 2.13/2.36      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 2.13/2.36         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 2.13/2.36           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 2.13/2.36      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.13/2.36  thf('44', plain,
% 2.13/2.36      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.13/2.36         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 2.13/2.36           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 2.13/2.36      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.13/2.36  thf('45', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.36         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['43', '44'])).
% 2.13/2.36  thf('46', plain,
% 2.13/2.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.36         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 2.13/2.36           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.13/2.36      inference('sup+', [status(thm)], ['42', '45'])).
% 2.13/2.36  thf('47', plain,
% 2.13/2.36      (![X0 : $i]:
% 2.13/2.36         ((k3_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A @ X0)
% 2.13/2.36           = (k1_enumset1 @ sk_B @ sk_C @ X0))),
% 2.13/2.36      inference('demod', [status(thm)], ['37', '46'])).
% 2.13/2.36  thf('48', plain,
% 2.13/2.36      (![X0 : $i]:
% 2.13/2.36         ((k2_enumset1 @ sk_B @ sk_C @ X0 @ X0)
% 2.13/2.36           = (k1_enumset1 @ sk_B @ sk_C @ X0))),
% 2.13/2.36      inference('demod', [status(thm)], ['36', '47'])).
% 2.13/2.36  thf(t98_enumset1, axiom,
% 2.13/2.36    (![A:$i,B:$i,C:$i]:
% 2.13/2.36     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 2.13/2.36  thf('49', plain,
% 2.13/2.36      (![X73 : $i, X74 : $i, X75 : $i]:
% 2.13/2.36         ((k1_enumset1 @ X73 @ X75 @ X74) = (k1_enumset1 @ X73 @ X74 @ X75))),
% 2.13/2.36      inference('cnf', [status(esa)], [t98_enumset1])).
% 2.13/2.36  thf('50', plain,
% 2.13/2.36      (((k1_enumset1 @ sk_B @ sk_A @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 2.13/2.36      inference('demod', [status(thm)], ['31', '48', '49'])).
% 2.13/2.36  thf(d1_enumset1, axiom,
% 2.13/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.13/2.36       ( ![E:$i]:
% 2.13/2.36         ( ( r2_hidden @ E @ D ) <=>
% 2.13/2.36           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.13/2.36  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.13/2.36  thf(zf_stmt_2, axiom,
% 2.13/2.36    (![E:$i,C:$i,B:$i,A:$i]:
% 2.13/2.36     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.13/2.36       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.13/2.36  thf(zf_stmt_3, axiom,
% 2.13/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.13/2.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.13/2.36       ( ![E:$i]:
% 2.13/2.36         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.13/2.36  thf('51', plain,
% 2.13/2.36      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.13/2.36         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 2.13/2.36          | (r2_hidden @ X20 @ X24)
% 2.13/2.36          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 2.13/2.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.13/2.36  thf('52', plain,
% 2.13/2.36      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.13/2.36         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 2.13/2.36          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 2.13/2.36      inference('simplify', [status(thm)], ['51'])).
% 2.13/2.36  thf('53', plain,
% 2.13/2.36      (![X0 : $i]:
% 2.13/2.36         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 2.13/2.36          | (zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B))),
% 2.13/2.36      inference('sup+', [status(thm)], ['50', '52'])).
% 2.13/2.36  thf(d2_tarski, axiom,
% 2.13/2.36    (![A:$i,B:$i,C:$i]:
% 2.13/2.36     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.13/2.36       ( ![D:$i]:
% 2.13/2.36         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.13/2.36  thf('54', plain,
% 2.13/2.36      (![X27 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.13/2.36         (~ (r2_hidden @ X31 @ X29)
% 2.13/2.36          | ((X31) = (X30))
% 2.13/2.36          | ((X31) = (X27))
% 2.13/2.36          | ((X29) != (k2_tarski @ X30 @ X27)))),
% 2.13/2.36      inference('cnf', [status(esa)], [d2_tarski])).
% 2.13/2.36  thf('55', plain,
% 2.13/2.36      (![X27 : $i, X30 : $i, X31 : $i]:
% 2.13/2.36         (((X31) = (X27))
% 2.13/2.36          | ((X31) = (X30))
% 2.13/2.36          | ~ (r2_hidden @ X31 @ (k2_tarski @ X30 @ X27)))),
% 2.13/2.36      inference('simplify', [status(thm)], ['54'])).
% 2.13/2.36  thf('56', plain,
% 2.13/2.36      (![X0 : $i]:
% 2.13/2.36         ((zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B)
% 2.13/2.36          | ((X0) = (sk_B))
% 2.13/2.36          | ((X0) = (sk_C)))),
% 2.13/2.36      inference('sup-', [status(thm)], ['53', '55'])).
% 2.13/2.36  thf('57', plain,
% 2.13/2.36      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.13/2.36         (((X16) != (X18)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 2.13/2.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.13/2.36  thf('58', plain,
% 2.13/2.36      (![X15 : $i, X17 : $i, X18 : $i]:
% 2.13/2.36         ~ (zip_tseitin_0 @ X18 @ X17 @ X18 @ X15)),
% 2.13/2.36      inference('simplify', [status(thm)], ['57'])).
% 2.13/2.36  thf('59', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 2.13/2.36      inference('sup-', [status(thm)], ['56', '58'])).
% 2.13/2.36  thf('60', plain, (((sk_A) != (sk_B))),
% 2.13/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.36  thf('61', plain, (((sk_A) != (sk_C))),
% 2.13/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.36  thf('62', plain, ($false),
% 2.13/2.36      inference('simplify_reflect-', [status(thm)], ['59', '60', '61'])).
% 2.13/2.36  
% 2.13/2.36  % SZS output end Refutation
% 2.13/2.36  
% 2.13/2.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
