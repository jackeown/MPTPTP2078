%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Z0xZ6nBWL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:57 EST 2020

% Result     : Theorem 5.39s
% Output     : Refutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 188 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  862 (1458 expanded)
%              Number of equality atoms :   81 ( 149 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('4',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 )
      | ( r2_hidden @ X37 @ X41 )
      | ( X41
       != ( k1_enumset1 @ X40 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ X37 @ ( k1_enumset1 @ X40 @ X39 @ X38 ) )
      | ( zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X33 != X32 )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ~ ( zip_tseitin_0 @ X32 @ X34 @ X35 @ X32 ) ),
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
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X17: $i] :
      ( r1_tarski @ X17 @ X17 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X19: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X21 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('19',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X54 ) @ X55 )
      | ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('44',plain,(
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('48',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','59'])).

thf('61',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('72',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','73'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('79',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Z0xZ6nBWL
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.39/5.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.39/5.59  % Solved by: fo/fo7.sh
% 5.39/5.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.39/5.59  % done 4162 iterations in 5.136s
% 5.39/5.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.39/5.59  % SZS output start Refutation
% 5.39/5.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.39/5.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.39/5.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.39/5.59  thf(sk_B_type, type, sk_B: $i).
% 5.39/5.59  thf(sk_A_type, type, sk_A: $i).
% 5.39/5.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.39/5.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 5.39/5.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.39/5.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.39/5.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.39/5.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.39/5.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.39/5.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.39/5.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.39/5.59  thf(t65_zfmisc_1, conjecture,
% 5.39/5.59    (![A:$i,B:$i]:
% 5.39/5.59     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 5.39/5.59       ( ~( r2_hidden @ B @ A ) ) ))).
% 5.39/5.59  thf(zf_stmt_0, negated_conjecture,
% 5.39/5.59    (~( ![A:$i,B:$i]:
% 5.39/5.59        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 5.39/5.59          ( ~( r2_hidden @ B @ A ) ) ) )),
% 5.39/5.59    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 5.39/5.59  thf('0', plain,
% 5.39/5.59      (((r2_hidden @ sk_B @ sk_A)
% 5.39/5.59        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 5.39/5.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.39/5.59  thf('1', plain,
% 5.39/5.59      (((r2_hidden @ sk_B @ sk_A)) | 
% 5.39/5.59       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.39/5.59      inference('split', [status(esa)], ['0'])).
% 5.39/5.59  thf('2', plain,
% 5.39/5.59      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 5.39/5.59      inference('split', [status(esa)], ['0'])).
% 5.39/5.59  thf(t70_enumset1, axiom,
% 5.39/5.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.39/5.59  thf('3', plain,
% 5.39/5.59      (![X45 : $i, X46 : $i]:
% 5.39/5.59         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 5.39/5.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.39/5.59  thf(d1_enumset1, axiom,
% 5.39/5.59    (![A:$i,B:$i,C:$i,D:$i]:
% 5.39/5.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 5.39/5.59       ( ![E:$i]:
% 5.39/5.59         ( ( r2_hidden @ E @ D ) <=>
% 5.39/5.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 5.39/5.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 5.39/5.59  thf(zf_stmt_2, axiom,
% 5.39/5.59    (![E:$i,C:$i,B:$i,A:$i]:
% 5.39/5.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 5.39/5.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 5.39/5.59  thf(zf_stmt_3, axiom,
% 5.39/5.59    (![A:$i,B:$i,C:$i,D:$i]:
% 5.39/5.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 5.39/5.59       ( ![E:$i]:
% 5.39/5.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 5.39/5.59  thf('4', plain,
% 5.39/5.59      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.39/5.59         ((zip_tseitin_0 @ X37 @ X38 @ X39 @ X40)
% 5.39/5.59          | (r2_hidden @ X37 @ X41)
% 5.39/5.59          | ((X41) != (k1_enumset1 @ X40 @ X39 @ X38)))),
% 5.39/5.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.39/5.59  thf('5', plain,
% 5.39/5.59      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 5.39/5.59         ((r2_hidden @ X37 @ (k1_enumset1 @ X40 @ X39 @ X38))
% 5.39/5.59          | (zip_tseitin_0 @ X37 @ X38 @ X39 @ X40))),
% 5.39/5.59      inference('simplify', [status(thm)], ['4'])).
% 5.39/5.59  thf('6', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.39/5.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 5.39/5.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 5.39/5.59      inference('sup+', [status(thm)], ['3', '5'])).
% 5.39/5.59  thf('7', plain,
% 5.39/5.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.39/5.59         (((X33) != (X32)) | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X32))),
% 5.39/5.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.39/5.59  thf('8', plain,
% 5.39/5.59      (![X32 : $i, X34 : $i, X35 : $i]:
% 5.39/5.59         ~ (zip_tseitin_0 @ X32 @ X34 @ X35 @ X32)),
% 5.39/5.59      inference('simplify', [status(thm)], ['7'])).
% 5.39/5.59  thf('9', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 5.39/5.59      inference('sup-', [status(thm)], ['6', '8'])).
% 5.39/5.59  thf(t69_enumset1, axiom,
% 5.39/5.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.39/5.59  thf('10', plain,
% 5.39/5.59      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 5.39/5.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.39/5.59  thf(d10_xboole_0, axiom,
% 5.39/5.59    (![A:$i,B:$i]:
% 5.39/5.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.39/5.59  thf('11', plain,
% 5.39/5.59      (![X16 : $i, X17 : $i]: ((r1_tarski @ X16 @ X17) | ((X16) != (X17)))),
% 5.39/5.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.39/5.59  thf('12', plain, (![X17 : $i]: (r1_tarski @ X17 @ X17)),
% 5.39/5.59      inference('simplify', [status(thm)], ['11'])).
% 5.39/5.59  thf(l32_xboole_1, axiom,
% 5.39/5.59    (![A:$i,B:$i]:
% 5.39/5.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.39/5.59  thf('13', plain,
% 5.39/5.59      (![X19 : $i, X21 : $i]:
% 5.39/5.59         (((k4_xboole_0 @ X19 @ X21) = (k1_xboole_0))
% 5.39/5.59          | ~ (r1_tarski @ X19 @ X21))),
% 5.39/5.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 5.39/5.59  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.39/5.59      inference('sup-', [status(thm)], ['12', '13'])).
% 5.39/5.59  thf(t48_xboole_1, axiom,
% 5.39/5.59    (![A:$i,B:$i]:
% 5.39/5.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.39/5.59  thf('15', plain,
% 5.39/5.59      (![X27 : $i, X28 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 5.39/5.59           = (k3_xboole_0 @ X27 @ X28))),
% 5.39/5.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.39/5.59  thf('16', plain,
% 5.39/5.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 5.39/5.59      inference('sup+', [status(thm)], ['14', '15'])).
% 5.39/5.59  thf(t3_boole, axiom,
% 5.39/5.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.39/5.59  thf('17', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 5.39/5.59      inference('cnf', [status(esa)], [t3_boole])).
% 5.39/5.59  thf('18', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 5.39/5.59      inference('demod', [status(thm)], ['16', '17'])).
% 5.39/5.59  thf(l27_zfmisc_1, axiom,
% 5.39/5.59    (![A:$i,B:$i]:
% 5.39/5.59     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 5.39/5.59  thf('19', plain,
% 5.39/5.59      (![X54 : $i, X55 : $i]:
% 5.39/5.59         ((r1_xboole_0 @ (k1_tarski @ X54) @ X55) | (r2_hidden @ X54 @ X55))),
% 5.39/5.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 5.39/5.59  thf(t83_xboole_1, axiom,
% 5.39/5.59    (![A:$i,B:$i]:
% 5.39/5.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.39/5.59  thf('20', plain,
% 5.39/5.59      (![X29 : $i, X30 : $i]:
% 5.39/5.59         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 5.39/5.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.39/5.59  thf('21', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         ((r2_hidden @ X1 @ X0)
% 5.39/5.59          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['19', '20'])).
% 5.39/5.59  thf('22', plain,
% 5.39/5.59      (![X27 : $i, X28 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 5.39/5.59           = (k3_xboole_0 @ X27 @ X28))),
% 5.39/5.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.39/5.59  thf('23', plain,
% 5.39/5.59      (![X27 : $i, X28 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 5.39/5.59           = (k3_xboole_0 @ X27 @ X28))),
% 5.39/5.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.39/5.59  thf('24', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.39/5.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.39/5.59      inference('sup+', [status(thm)], ['22', '23'])).
% 5.39/5.59  thf(d5_xboole_0, axiom,
% 5.39/5.59    (![A:$i,B:$i,C:$i]:
% 5.39/5.59     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.39/5.59       ( ![D:$i]:
% 5.39/5.59         ( ( r2_hidden @ D @ C ) <=>
% 5.39/5.59           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.39/5.59  thf('25', plain,
% 5.39/5.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X10 @ X9)
% 5.39/5.59          | ~ (r2_hidden @ X10 @ X8)
% 5.39/5.59          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 5.39/5.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.39/5.59  thf('26', plain,
% 5.39/5.59      (![X7 : $i, X8 : $i, X10 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X10 @ X8)
% 5.39/5.59          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 5.39/5.59      inference('simplify', [status(thm)], ['25'])).
% 5.39/5.59  thf('27', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 5.39/5.59          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['24', '26'])).
% 5.39/5.59  thf('28', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X2 @ 
% 5.39/5.59             (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 5.39/5.59          | (r2_hidden @ X0 @ X1)
% 5.39/5.59          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['21', '27'])).
% 5.39/5.59  thf('29', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 5.39/5.59      inference('demod', [status(thm)], ['16', '17'])).
% 5.39/5.59  thf('30', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 5.39/5.59          | (r2_hidden @ X0 @ X1)
% 5.39/5.59          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 5.39/5.59      inference('demod', [status(thm)], ['28', '29'])).
% 5.39/5.59  thf(d4_xboole_0, axiom,
% 5.39/5.59    (![A:$i,B:$i,C:$i]:
% 5.39/5.59     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 5.39/5.59       ( ![D:$i]:
% 5.39/5.59         ( ( r2_hidden @ D @ C ) <=>
% 5.39/5.59           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.39/5.59  thf('31', plain,
% 5.39/5.59      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X4 @ X3)
% 5.39/5.59          | (r2_hidden @ X4 @ X1)
% 5.39/5.59          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 5.39/5.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.39/5.59  thf('32', plain,
% 5.39/5.59      (![X1 : $i, X2 : $i, X4 : $i]:
% 5.39/5.59         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 5.39/5.59      inference('simplify', [status(thm)], ['31'])).
% 5.39/5.59  thf('33', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 5.39/5.59          | (r2_hidden @ X0 @ X1))),
% 5.39/5.59      inference('clc', [status(thm)], ['30', '32'])).
% 5.39/5.59  thf('34', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 5.39/5.59          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['18', '33'])).
% 5.39/5.59  thf('35', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 5.39/5.59          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['10', '34'])).
% 5.39/5.59  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.39/5.59      inference('sup-', [status(thm)], ['9', '35'])).
% 5.39/5.59  thf('37', plain,
% 5.39/5.59      ((~ (r2_hidden @ sk_B @ sk_A)
% 5.39/5.59        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.39/5.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.39/5.59  thf('38', plain,
% 5.39/5.59      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 5.39/5.59         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.39/5.59      inference('split', [status(esa)], ['37'])).
% 5.39/5.59  thf('39', plain,
% 5.39/5.59      (![X7 : $i, X8 : $i, X10 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X10 @ X8)
% 5.39/5.59          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 5.39/5.59      inference('simplify', [status(thm)], ['25'])).
% 5.39/5.59  thf('40', plain,
% 5.39/5.59      ((![X0 : $i]:
% 5.39/5.59          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 5.39/5.59         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.39/5.59      inference('sup-', [status(thm)], ['38', '39'])).
% 5.39/5.59  thf('41', plain,
% 5.39/5.59      ((~ (r2_hidden @ sk_B @ sk_A))
% 5.39/5.59         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.39/5.59      inference('sup-', [status(thm)], ['36', '40'])).
% 5.39/5.59  thf('42', plain,
% 5.39/5.59      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 5.39/5.59       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['2', '41'])).
% 5.39/5.59  thf('43', plain,
% 5.39/5.59      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 5.39/5.59       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.39/5.59      inference('split', [status(esa)], ['37'])).
% 5.39/5.59  thf('44', plain,
% 5.39/5.59      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 5.39/5.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.39/5.59  thf('45', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         ((r2_hidden @ X1 @ X0)
% 5.39/5.59          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['19', '20'])).
% 5.39/5.59  thf('46', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) = (k1_tarski @ X0))
% 5.39/5.59          | (r2_hidden @ X0 @ X1))),
% 5.39/5.59      inference('sup+', [status(thm)], ['44', '45'])).
% 5.39/5.59  thf('47', plain,
% 5.39/5.59      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.39/5.59         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 5.39/5.59          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 5.39/5.59          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.39/5.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.39/5.59  thf('48', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 5.39/5.59      inference('cnf', [status(esa)], [t3_boole])).
% 5.39/5.59  thf('49', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 5.39/5.59      inference('cnf', [status(esa)], [t3_boole])).
% 5.39/5.59  thf('50', plain,
% 5.39/5.59      (![X27 : $i, X28 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X27 @ X28))
% 5.39/5.59           = (k3_xboole_0 @ X27 @ X28))),
% 5.39/5.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.39/5.59  thf('51', plain,
% 5.39/5.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 5.39/5.59      inference('sup+', [status(thm)], ['49', '50'])).
% 5.39/5.59  thf(t100_xboole_1, axiom,
% 5.39/5.59    (![A:$i,B:$i]:
% 5.39/5.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.39/5.59  thf('52', plain,
% 5.39/5.59      (![X22 : $i, X23 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X22 @ X23)
% 5.39/5.59           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 5.39/5.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.39/5.59  thf('53', plain,
% 5.39/5.59      (![X0 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 5.39/5.59           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 5.39/5.59      inference('sup+', [status(thm)], ['51', '52'])).
% 5.39/5.59  thf('54', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 5.39/5.59      inference('cnf', [status(esa)], [t3_boole])).
% 5.39/5.59  thf('55', plain,
% 5.39/5.59      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 5.39/5.59      inference('demod', [status(thm)], ['53', '54'])).
% 5.39/5.59  thf('56', plain,
% 5.39/5.59      (((k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 5.39/5.59      inference('sup+', [status(thm)], ['48', '55'])).
% 5.39/5.59  thf(t1_xboole_0, axiom,
% 5.39/5.59    (![A:$i,B:$i,C:$i]:
% 5.39/5.59     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 5.39/5.59       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 5.39/5.59  thf('57', plain,
% 5.39/5.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X12 @ X13)
% 5.39/5.59          | ~ (r2_hidden @ X12 @ X14)
% 5.39/5.59          | ~ (r2_hidden @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 5.39/5.59      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.39/5.59  thf('58', plain,
% 5.39/5.59      (![X0 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.39/5.59          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.39/5.59          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 5.39/5.59      inference('sup-', [status(thm)], ['56', '57'])).
% 5.39/5.59  thf('59', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.39/5.59      inference('simplify', [status(thm)], ['58'])).
% 5.39/5.59  thf('60', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.39/5.59          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['47', '59'])).
% 5.39/5.59  thf('61', plain,
% 5.39/5.59      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.39/5.59         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 5.39/5.59          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 5.39/5.59          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.39/5.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.39/5.59  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.39/5.59      inference('simplify', [status(thm)], ['58'])).
% 5.39/5.59  thf('63', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 5.39/5.59          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['61', '62'])).
% 5.39/5.59  thf('64', plain,
% 5.39/5.59      (![X7 : $i, X8 : $i, X10 : $i]:
% 5.39/5.59         (~ (r2_hidden @ X10 @ X8)
% 5.39/5.59          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 5.39/5.59      inference('simplify', [status(thm)], ['25'])).
% 5.39/5.59  thf('65', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.39/5.59         (((k1_xboole_0) = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 5.39/5.59          | ~ (r2_hidden @ 
% 5.39/5.59               (sk_D @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 5.39/5.59      inference('sup-', [status(thm)], ['63', '64'])).
% 5.39/5.59  thf('66', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 5.39/5.59          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 5.39/5.59      inference('sup-', [status(thm)], ['60', '65'])).
% 5.39/5.59  thf('67', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.39/5.59      inference('simplify', [status(thm)], ['66'])).
% 5.39/5.59  thf('68', plain,
% 5.39/5.59      (![X22 : $i, X23 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X22 @ X23)
% 5.39/5.59           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 5.39/5.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.39/5.59  thf('69', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 5.39/5.59           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.39/5.59      inference('sup+', [status(thm)], ['67', '68'])).
% 5.39/5.59  thf('70', plain,
% 5.39/5.59      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 5.39/5.59      inference('demod', [status(thm)], ['53', '54'])).
% 5.39/5.59  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.39/5.59      inference('sup-', [status(thm)], ['12', '13'])).
% 5.39/5.59  thf('72', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.39/5.59      inference('demod', [status(thm)], ['70', '71'])).
% 5.39/5.59  thf('73', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 5.39/5.59      inference('demod', [status(thm)], ['69', '72'])).
% 5.39/5.59  thf('74', plain,
% 5.39/5.59      (![X0 : $i, X1 : $i]:
% 5.39/5.59         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 5.39/5.59          | (r2_hidden @ X0 @ X1))),
% 5.39/5.59      inference('sup+', [status(thm)], ['46', '73'])).
% 5.39/5.59  thf('75', plain,
% 5.39/5.59      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 5.39/5.59         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.39/5.59      inference('split', [status(esa)], ['0'])).
% 5.39/5.59  thf('76', plain,
% 5.39/5.59      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 5.39/5.59         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.39/5.59      inference('sup-', [status(thm)], ['74', '75'])).
% 5.39/5.59  thf('77', plain,
% 5.39/5.59      (((r2_hidden @ sk_B @ sk_A))
% 5.39/5.59         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.39/5.59      inference('simplify', [status(thm)], ['76'])).
% 5.39/5.59  thf('78', plain,
% 5.39/5.59      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 5.39/5.59      inference('split', [status(esa)], ['37'])).
% 5.39/5.59  thf('79', plain,
% 5.39/5.59      (((r2_hidden @ sk_B @ sk_A)) | 
% 5.39/5.59       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.39/5.59      inference('sup-', [status(thm)], ['77', '78'])).
% 5.39/5.59  thf('80', plain, ($false),
% 5.39/5.59      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '79'])).
% 5.39/5.59  
% 5.39/5.59  % SZS output end Refutation
% 5.39/5.59  
% 5.39/5.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
