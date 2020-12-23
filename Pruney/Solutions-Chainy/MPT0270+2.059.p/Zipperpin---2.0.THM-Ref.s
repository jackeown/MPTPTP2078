%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HJXkeZYFu1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:19 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 240 expanded)
%              Number of leaves         :   17 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  901 (2793 expanded)
%              Number of equality atoms :   80 ( 252 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
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
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_A )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ sk_B )
        | ( ( k1_tarski @ sk_A )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
        | ( ( k1_tarski @ sk_A )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_A )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( k1_tarski @ sk_A )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('47',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('54',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('63',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','49','62'])).

thf('64',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['51','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HJXkeZYFu1
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:20:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.82/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.01  % Solved by: fo/fo7.sh
% 0.82/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.01  % done 745 iterations in 0.547s
% 0.82/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.01  % SZS output start Refutation
% 0.82/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.82/1.01  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.82/1.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.82/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.82/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.01  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.82/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.01  thf(t67_zfmisc_1, conjecture,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.82/1.01       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.82/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.01    (~( ![A:$i,B:$i]:
% 0.82/1.01        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.82/1.01          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.82/1.01    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.82/1.01  thf('0', plain,
% 0.82/1.01      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.82/1.01        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('1', plain,
% 0.82/1.01      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.82/1.01      inference('split', [status(esa)], ['0'])).
% 0.82/1.01  thf('2', plain,
% 0.82/1.01      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.82/1.01       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.82/1.01      inference('split', [status(esa)], ['0'])).
% 0.82/1.01  thf(t70_enumset1, axiom,
% 0.82/1.01    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.82/1.01  thf('3', plain,
% 0.82/1.01      (![X21 : $i, X22 : $i]:
% 0.82/1.01         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.82/1.01      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.01  thf(d1_enumset1, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.01     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.82/1.01       ( ![E:$i]:
% 0.82/1.01         ( ( r2_hidden @ E @ D ) <=>
% 0.82/1.01           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.82/1.01  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.82/1.01  thf(zf_stmt_2, axiom,
% 0.82/1.01    (![E:$i,C:$i,B:$i,A:$i]:
% 0.82/1.01     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.82/1.01       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.82/1.01  thf(zf_stmt_3, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.01     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.82/1.01       ( ![E:$i]:
% 0.82/1.01         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.82/1.01  thf('4', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.82/1.01         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.82/1.01          | (r2_hidden @ X13 @ X17)
% 0.82/1.01          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.01  thf('5', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.82/1.01         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.82/1.01          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.82/1.01      inference('simplify', [status(thm)], ['4'])).
% 0.82/1.01  thf('6', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.82/1.01          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.82/1.01      inference('sup+', [status(thm)], ['3', '5'])).
% 0.82/1.01  thf('7', plain,
% 0.82/1.01      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.01         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.01  thf('8', plain,
% 0.82/1.01      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.82/1.01      inference('simplify', [status(thm)], ['7'])).
% 0.82/1.01  thf('9', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['6', '8'])).
% 0.82/1.01  thf(t69_enumset1, axiom,
% 0.82/1.01    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.82/1.01  thf('10', plain,
% 0.82/1.01      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.82/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.01  thf('11', plain,
% 0.82/1.01      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.82/1.01         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.82/1.01          | ((X9) = (X10))
% 0.82/1.01          | ((X9) = (X11))
% 0.82/1.01          | ((X9) = (X12)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.01  thf(d5_xboole_0, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i]:
% 0.82/1.01     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.82/1.01       ( ![D:$i]:
% 0.82/1.01         ( ( r2_hidden @ D @ C ) <=>
% 0.82/1.01           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.82/1.01  thf('12', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.82/1.01         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.82/1.01          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('13', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.82/1.01          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.82/1.01      inference('eq_fact', [status(thm)], ['12'])).
% 0.82/1.01  thf('14', plain,
% 0.82/1.01      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.82/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.01  thf('15', plain,
% 0.82/1.01      (![X21 : $i, X22 : $i]:
% 0.82/1.01         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.82/1.01      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.01  thf('16', plain,
% 0.82/1.01      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X18 @ X17)
% 0.82/1.01          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.82/1.01          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.01  thf('17', plain,
% 0.82/1.01      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.82/1.01         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.82/1.01          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['16'])).
% 0.82/1.01  thf('18', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.82/1.01          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['15', '17'])).
% 0.82/1.01  thf('19', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.82/1.01          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['14', '18'])).
% 0.82/1.01  thf('20', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.82/1.01          | ~ (zip_tseitin_0 @ 
% 0.82/1.01               (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['13', '19'])).
% 0.82/1.01  thf('21', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.82/1.01          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.82/1.01          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.82/1.01          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['11', '20'])).
% 0.82/1.01  thf('22', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.82/1.01          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['21'])).
% 0.82/1.01  thf('23', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.82/1.01         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.82/1.01          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('24', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.82/1.01         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.82/1.01          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('25', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.82/1.01          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.82/1.01          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['23', '24'])).
% 0.82/1.01  thf('26', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.82/1.01      inference('simplify', [status(thm)], ['25'])).
% 0.82/1.01  thf('27', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.82/1.01          | ((k1_tarski @ X0)
% 0.82/1.01              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k1_tarski @ X0)
% 0.82/1.01              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))))),
% 0.82/1.01      inference('sup+', [status(thm)], ['22', '26'])).
% 0.82/1.01  thf('28', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (((k1_tarski @ X0)
% 0.82/1.01            = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.82/1.01          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['27'])).
% 0.82/1.01  thf('29', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X4 @ X3)
% 0.82/1.01          | ~ (r2_hidden @ X4 @ X2)
% 0.82/1.01          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('30', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X4 @ X2)
% 0.82/1.01          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['29'])).
% 0.82/1.01  thf('31', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.82/1.01          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.82/1.01          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['28', '30'])).
% 0.82/1.01  thf('32', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.82/1.01          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['31'])).
% 0.82/1.01  thf('33', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.82/1.01          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['10', '32'])).
% 0.82/1.01  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['9', '33'])).
% 0.82/1.01  thf('35', plain,
% 0.82/1.01      (((r2_hidden @ sk_A @ sk_B)
% 0.82/1.01        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('36', plain,
% 0.82/1.01      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.82/1.01      inference('split', [status(esa)], ['35'])).
% 0.82/1.01  thf('37', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.82/1.01          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['21'])).
% 0.82/1.01  thf('38', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.82/1.01          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.82/1.01      inference('eq_fact', [status(thm)], ['12'])).
% 0.82/1.01  thf('39', plain,
% 0.82/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.82/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.82/1.01      inference('split', [status(esa)], ['0'])).
% 0.82/1.01  thf('40', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X4 @ X2)
% 0.82/1.01          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['29'])).
% 0.82/1.01  thf('41', plain,
% 0.82/1.01      ((![X0 : $i]:
% 0.82/1.01          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.82/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['39', '40'])).
% 0.82/1.01  thf('42', plain,
% 0.82/1.01      ((![X0 : $i]:
% 0.82/1.01          (((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.82/1.01           | ~ (r2_hidden @ 
% 0.82/1.01                (sk_D @ (k1_tarski @ sk_A) @ X0 @ (k1_tarski @ sk_A)) @ sk_B)))
% 0.82/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['38', '41'])).
% 0.82/1.01  thf('43', plain,
% 0.82/1.01      ((![X0 : $i]:
% 0.82/1.01          (~ (r2_hidden @ sk_A @ sk_B)
% 0.82/1.01           | ((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.82/1.01           | ((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.82/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.82/1.01      inference('sup-', [status(thm)], ['37', '42'])).
% 0.82/1.01  thf('44', plain,
% 0.82/1.01      ((![X0 : $i]:
% 0.82/1.01          (((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.82/1.01           | ~ (r2_hidden @ sk_A @ sk_B)))
% 0.82/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.82/1.01      inference('simplify', [status(thm)], ['43'])).
% 0.82/1.01  thf('45', plain,
% 0.82/1.01      ((![X0 : $i]:
% 0.82/1.01          ((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))
% 0.82/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.82/1.01             ((r2_hidden @ sk_A @ sk_B)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['36', '44'])).
% 0.82/1.01  thf('46', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X4 @ X2)
% 0.82/1.01          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['29'])).
% 0.82/1.01  thf('47', plain,
% 0.82/1.01      ((![X0 : $i, X1 : $i]:
% 0.82/1.01          (~ (r2_hidden @ X1 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X1 @ X0)))
% 0.82/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.82/1.01             ((r2_hidden @ sk_A @ sk_B)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['45', '46'])).
% 0.82/1.01  thf('48', plain,
% 0.82/1.01      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))
% 0.82/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.82/1.01             ((r2_hidden @ sk_A @ sk_B)))),
% 0.82/1.01      inference('condensation', [status(thm)], ['47'])).
% 0.82/1.01  thf('49', plain,
% 0.82/1.01      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.82/1.01       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.82/1.01      inference('sup-', [status(thm)], ['34', '48'])).
% 0.82/1.01  thf('50', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.82/1.01      inference('sat_resolution*', [status(thm)], ['2', '49'])).
% 0.82/1.01  thf('51', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.82/1.01      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.82/1.01  thf('52', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.82/1.01          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['21'])).
% 0.82/1.01  thf('53', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.82/1.01          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.82/1.01      inference('eq_fact', [status(thm)], ['12'])).
% 0.82/1.01  thf('54', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.82/1.01         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('55', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.82/1.01          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.82/1.01          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['53', '54'])).
% 0.82/1.01  thf('56', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.82/1.01          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['55'])).
% 0.82/1.01  thf('57', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.82/1.01          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.82/1.01      inference('eq_fact', [status(thm)], ['12'])).
% 0.82/1.01  thf('58', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.82/1.01      inference('clc', [status(thm)], ['56', '57'])).
% 0.82/1.01  thf('59', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ X0 @ X1)
% 0.82/1.01          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.82/1.01          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.82/1.01      inference('sup+', [status(thm)], ['52', '58'])).
% 0.82/1.01  thf('60', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.82/1.01          | (r2_hidden @ X0 @ X1))),
% 0.82/1.01      inference('simplify', [status(thm)], ['59'])).
% 0.82/1.01  thf('61', plain,
% 0.82/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.82/1.01         <= (~
% 0.82/1.01             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.82/1.01      inference('split', [status(esa)], ['35'])).
% 0.82/1.01  thf('62', plain,
% 0.82/1.01      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.82/1.01       ((r2_hidden @ sk_A @ sk_B))),
% 0.82/1.01      inference('split', [status(esa)], ['35'])).
% 0.82/1.01  thf('63', plain,
% 0.82/1.01      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.82/1.01      inference('sat_resolution*', [status(thm)], ['2', '49', '62'])).
% 0.82/1.01  thf('64', plain,
% 0.82/1.01      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.82/1.01      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.82/1.01  thf('65', plain,
% 0.82/1.01      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.82/1.01      inference('sup-', [status(thm)], ['60', '64'])).
% 0.82/1.01  thf('66', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.82/1.01      inference('simplify', [status(thm)], ['65'])).
% 0.82/1.01  thf('67', plain, ($false), inference('demod', [status(thm)], ['51', '66'])).
% 0.82/1.01  
% 0.82/1.01  % SZS output end Refutation
% 0.82/1.01  
% 0.82/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
