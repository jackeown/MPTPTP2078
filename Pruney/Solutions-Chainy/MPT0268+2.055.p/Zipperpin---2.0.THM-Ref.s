%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J4lDffOz5x

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:59 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 270 expanded)
%              Number of leaves         :   17 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          : 1048 (3135 expanded)
%              Number of equality atoms :   98 ( 285 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
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
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

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
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_B )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('70',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','73'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('76',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('77',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','49','76'])).

thf('78',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['75','77'])).

thf('79',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['51','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J4lDffOz5x
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.37/1.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.37/1.58  % Solved by: fo/fo7.sh
% 1.37/1.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.58  % done 1256 iterations in 1.129s
% 1.37/1.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.37/1.58  % SZS output start Refutation
% 1.37/1.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.37/1.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.37/1.58  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.37/1.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.37/1.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.37/1.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.37/1.58  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.58  thf(t65_zfmisc_1, conjecture,
% 1.37/1.58    (![A:$i,B:$i]:
% 1.37/1.58     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.37/1.58       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.37/1.58  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.58    (~( ![A:$i,B:$i]:
% 1.37/1.58        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.37/1.58          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.37/1.58    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.37/1.58  thf('0', plain,
% 1.37/1.58      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.37/1.58        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('1', plain,
% 1.37/1.58      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.37/1.58      inference('split', [status(esa)], ['0'])).
% 1.37/1.58  thf('2', plain,
% 1.37/1.58      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.37/1.58       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.37/1.58      inference('split', [status(esa)], ['0'])).
% 1.37/1.58  thf(t70_enumset1, axiom,
% 1.37/1.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.37/1.58  thf('3', plain,
% 1.37/1.58      (![X21 : $i, X22 : $i]:
% 1.37/1.58         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 1.37/1.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.37/1.58  thf(d1_enumset1, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.37/1.58       ( ![E:$i]:
% 1.37/1.58         ( ( r2_hidden @ E @ D ) <=>
% 1.37/1.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.37/1.58  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.37/1.58  thf(zf_stmt_2, axiom,
% 1.37/1.58    (![E:$i,C:$i,B:$i,A:$i]:
% 1.37/1.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.37/1.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.37/1.58  thf(zf_stmt_3, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.37/1.58       ( ![E:$i]:
% 1.37/1.58         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.37/1.58  thf('4', plain,
% 1.37/1.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.37/1.58         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 1.37/1.58          | (r2_hidden @ X13 @ X17)
% 1.37/1.58          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.37/1.58  thf('5', plain,
% 1.37/1.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.37/1.58         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 1.37/1.58          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 1.37/1.58      inference('simplify', [status(thm)], ['4'])).
% 1.37/1.58  thf('6', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.37/1.58          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.37/1.58      inference('sup+', [status(thm)], ['3', '5'])).
% 1.37/1.58  thf('7', plain,
% 1.37/1.58      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.37/1.58         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.37/1.58  thf('8', plain,
% 1.37/1.58      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 1.37/1.58      inference('simplify', [status(thm)], ['7'])).
% 1.37/1.58  thf('9', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.37/1.58      inference('sup-', [status(thm)], ['6', '8'])).
% 1.37/1.58  thf(t69_enumset1, axiom,
% 1.37/1.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.37/1.58  thf('10', plain,
% 1.37/1.58      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 1.37/1.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.37/1.58  thf('11', plain,
% 1.37/1.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.37/1.58         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 1.37/1.58          | ((X9) = (X10))
% 1.37/1.58          | ((X9) = (X11))
% 1.37/1.58          | ((X9) = (X12)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.37/1.58  thf(d5_xboole_0, axiom,
% 1.37/1.58    (![A:$i,B:$i,C:$i]:
% 1.37/1.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.37/1.58       ( ![D:$i]:
% 1.37/1.58         ( ( r2_hidden @ D @ C ) <=>
% 1.37/1.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.37/1.58  thf('12', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.37/1.58         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.37/1.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.37/1.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.37/1.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.37/1.58  thf('13', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.37/1.58         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.37/1.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.37/1.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.37/1.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.37/1.58  thf('14', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.37/1.58          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.37/1.58          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.37/1.58          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['12', '13'])).
% 1.37/1.58  thf('15', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.37/1.58          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.37/1.58      inference('simplify', [status(thm)], ['14'])).
% 1.37/1.58  thf('16', plain,
% 1.37/1.58      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 1.37/1.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.37/1.58  thf('17', plain,
% 1.37/1.58      (![X21 : $i, X22 : $i]:
% 1.37/1.58         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 1.37/1.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.37/1.58  thf('18', plain,
% 1.37/1.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X18 @ X17)
% 1.37/1.58          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 1.37/1.58          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.37/1.58  thf('19', plain,
% 1.37/1.58      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 1.37/1.58         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 1.37/1.58          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['18'])).
% 1.37/1.58  thf('20', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.37/1.58          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.37/1.58      inference('sup-', [status(thm)], ['17', '19'])).
% 1.37/1.58  thf('21', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.37/1.58          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.37/1.58      inference('sup-', [status(thm)], ['16', '20'])).
% 1.37/1.58  thf('22', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.37/1.58          | ~ (zip_tseitin_0 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X0 @ X0 @ 
% 1.37/1.58               X0))),
% 1.37/1.58      inference('sup-', [status(thm)], ['15', '21'])).
% 1.37/1.58  thf('23', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.37/1.58          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.37/1.58          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.37/1.58          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['11', '22'])).
% 1.37/1.58  thf('24', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.37/1.58          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['23'])).
% 1.37/1.58  thf('25', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.37/1.58         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.37/1.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.37/1.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.37/1.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.37/1.58  thf('26', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.58      inference('eq_fact', [status(thm)], ['25'])).
% 1.37/1.58  thf('27', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.37/1.58          | ((k1_tarski @ X0)
% 1.37/1.58              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 1.37/1.58          | ((k1_tarski @ X0)
% 1.37/1.58              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))))),
% 1.37/1.58      inference('sup+', [status(thm)], ['24', '26'])).
% 1.37/1.58  thf('28', plain,
% 1.37/1.58      (![X0 : $i]:
% 1.37/1.58         (((k1_tarski @ X0)
% 1.37/1.58            = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 1.37/1.58          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['27'])).
% 1.37/1.58  thf('29', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X4 @ X3)
% 1.37/1.58          | ~ (r2_hidden @ X4 @ X2)
% 1.37/1.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.37/1.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.37/1.58  thf('30', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X4 @ X2)
% 1.37/1.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.58  thf('31', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.37/1.58          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.37/1.58          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['28', '30'])).
% 1.37/1.58  thf('32', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.37/1.58          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['31'])).
% 1.37/1.58  thf('33', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 1.37/1.58          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['10', '32'])).
% 1.37/1.58  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.37/1.58      inference('sup-', [status(thm)], ['9', '33'])).
% 1.37/1.58  thf('35', plain,
% 1.37/1.58      (((r2_hidden @ sk_B @ sk_A)
% 1.37/1.58        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.58  thf('36', plain,
% 1.37/1.58      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.37/1.58      inference('split', [status(esa)], ['35'])).
% 1.37/1.58  thf('37', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.37/1.58          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['23'])).
% 1.37/1.58  thf('38', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.58      inference('eq_fact', [status(thm)], ['25'])).
% 1.37/1.58  thf('39', plain,
% 1.37/1.58      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.37/1.58         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.37/1.58      inference('split', [status(esa)], ['0'])).
% 1.37/1.58  thf('40', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X4 @ X2)
% 1.37/1.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.58  thf('41', plain,
% 1.37/1.58      ((![X0 : $i]:
% 1.37/1.58          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.37/1.58         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.37/1.58      inference('sup-', [status(thm)], ['39', '40'])).
% 1.37/1.58  thf('42', plain,
% 1.37/1.58      ((![X0 : $i]:
% 1.37/1.58          (((k1_tarski @ sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 1.37/1.58           | ~ (r2_hidden @ 
% 1.37/1.58                (sk_D @ (k1_tarski @ sk_B) @ X0 @ (k1_tarski @ sk_B)) @ sk_A)))
% 1.37/1.58         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.37/1.58      inference('sup-', [status(thm)], ['38', '41'])).
% 1.37/1.58  thf('43', plain,
% 1.37/1.58      (((~ (r2_hidden @ sk_B @ sk_A)
% 1.37/1.58         | ((k1_tarski @ sk_B)
% 1.37/1.58             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 1.37/1.58         | ((k1_tarski @ sk_B)
% 1.37/1.58             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))))
% 1.37/1.58         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.37/1.58      inference('sup-', [status(thm)], ['37', '42'])).
% 1.37/1.58  thf('44', plain,
% 1.37/1.58      (((((k1_tarski @ sk_B)
% 1.37/1.58           = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 1.37/1.58         | ~ (r2_hidden @ sk_B @ sk_A)))
% 1.37/1.58         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.37/1.58      inference('simplify', [status(thm)], ['43'])).
% 1.37/1.58  thf('45', plain,
% 1.37/1.58      ((((k1_tarski @ sk_B)
% 1.37/1.58          = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 1.37/1.58         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.37/1.58             ((r2_hidden @ sk_B @ sk_A)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['36', '44'])).
% 1.37/1.58  thf('46', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X4 @ X2)
% 1.37/1.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.58  thf('47', plain,
% 1.37/1.58      ((![X0 : $i]:
% 1.37/1.58          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.37/1.58           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.37/1.58         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.37/1.58             ((r2_hidden @ sk_B @ sk_A)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['45', '46'])).
% 1.37/1.58  thf('48', plain,
% 1.37/1.58      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))
% 1.37/1.58         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.37/1.58             ((r2_hidden @ sk_B @ sk_A)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['47'])).
% 1.37/1.58  thf('49', plain,
% 1.37/1.58      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.37/1.58       ~ ((r2_hidden @ sk_B @ sk_A))),
% 1.37/1.58      inference('sup-', [status(thm)], ['34', '48'])).
% 1.37/1.58  thf('50', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 1.37/1.58      inference('sat_resolution*', [status(thm)], ['2', '49'])).
% 1.37/1.58  thf('51', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.37/1.58      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 1.37/1.58  thf('52', plain,
% 1.37/1.58      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 1.37/1.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.37/1.58  thf('53', plain,
% 1.37/1.58      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.37/1.58         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 1.37/1.58          | ((X9) = (X10))
% 1.37/1.58          | ((X9) = (X11))
% 1.37/1.58          | ((X9) = (X12)))),
% 1.37/1.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.37/1.58  thf('54', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.58      inference('eq_fact', [status(thm)], ['25'])).
% 1.37/1.58  thf('55', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.37/1.58          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.37/1.58      inference('sup-', [status(thm)], ['16', '20'])).
% 1.37/1.58  thf('56', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.37/1.58          | ~ (zip_tseitin_0 @ 
% 1.37/1.58               (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.37/1.58      inference('sup-', [status(thm)], ['54', '55'])).
% 1.37/1.58  thf('57', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.37/1.58          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.37/1.58          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.37/1.58          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['53', '56'])).
% 1.37/1.58  thf('58', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.37/1.58          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['57'])).
% 1.37/1.58  thf('59', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.58      inference('eq_fact', [status(thm)], ['25'])).
% 1.37/1.58  thf('60', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.37/1.58         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.37/1.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.37/1.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.37/1.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.37/1.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.37/1.58  thf('61', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.37/1.58          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.37/1.58          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.58      inference('sup-', [status(thm)], ['59', '60'])).
% 1.37/1.58  thf('62', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.37/1.58          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['61'])).
% 1.37/1.58  thf('63', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.58      inference('eq_fact', [status(thm)], ['25'])).
% 1.37/1.58  thf('64', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.37/1.58          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.37/1.58      inference('clc', [status(thm)], ['62', '63'])).
% 1.37/1.58  thf('65', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ X0 @ X1)
% 1.37/1.58          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.37/1.58          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.37/1.58      inference('sup+', [status(thm)], ['58', '64'])).
% 1.37/1.58  thf('66', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.37/1.58          | (r2_hidden @ X0 @ X1))),
% 1.37/1.58      inference('simplify', [status(thm)], ['65'])).
% 1.37/1.58  thf('67', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((k1_tarski @ X0) = (k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 1.37/1.58          | (r2_hidden @ X0 @ X1))),
% 1.37/1.58      inference('sup+', [status(thm)], ['52', '66'])).
% 1.37/1.58  thf('68', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.58      inference('eq_fact', [status(thm)], ['25'])).
% 1.37/1.58  thf('69', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.37/1.58          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.37/1.58      inference('clc', [status(thm)], ['62', '63'])).
% 1.37/1.58  thf('70', plain,
% 1.37/1.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.37/1.58         (~ (r2_hidden @ X4 @ X2)
% 1.37/1.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.58  thf('71', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.58         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.37/1.58          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 1.37/1.58      inference('sup-', [status(thm)], ['69', '70'])).
% 1.37/1.58  thf('72', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.37/1.58          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.37/1.58      inference('sup-', [status(thm)], ['68', '71'])).
% 1.37/1.58  thf('73', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.37/1.58      inference('simplify', [status(thm)], ['72'])).
% 1.37/1.58  thf('74', plain,
% 1.37/1.58      (![X0 : $i, X1 : $i]:
% 1.37/1.58         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.37/1.58          | (r2_hidden @ X0 @ X1))),
% 1.37/1.58      inference('sup+', [status(thm)], ['67', '73'])).
% 1.37/1.58  thf('75', plain,
% 1.37/1.58      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.37/1.58         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.37/1.58      inference('split', [status(esa)], ['35'])).
% 1.37/1.58  thf('76', plain,
% 1.37/1.58      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.37/1.58       ((r2_hidden @ sk_B @ sk_A))),
% 1.37/1.58      inference('split', [status(esa)], ['35'])).
% 1.37/1.58  thf('77', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.37/1.58      inference('sat_resolution*', [status(thm)], ['2', '49', '76'])).
% 1.37/1.58  thf('78', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 1.37/1.58      inference('simpl_trail', [status(thm)], ['75', '77'])).
% 1.37/1.58  thf('79', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 1.37/1.58      inference('sup-', [status(thm)], ['74', '78'])).
% 1.37/1.58  thf('80', plain, ((r2_hidden @ sk_B @ sk_A)),
% 1.37/1.58      inference('simplify', [status(thm)], ['79'])).
% 1.37/1.58  thf('81', plain, ($false), inference('demod', [status(thm)], ['51', '80'])).
% 1.37/1.58  
% 1.37/1.58  % SZS output end Refutation
% 1.37/1.58  
% 1.37/1.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
