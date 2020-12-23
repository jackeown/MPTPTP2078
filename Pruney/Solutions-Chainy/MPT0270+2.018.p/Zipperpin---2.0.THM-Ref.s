%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MVukGSYmHx

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:14 EST 2020

% Result     : Theorem 5.04s
% Output     : Refutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 189 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  826 (1656 expanded)
%              Number of equality atoms :   74 ( 143 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_enumset1 @ X50 @ X50 @ X51 )
      = ( k2_tarski @ X50 @ X51 ) ) ),
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

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 )
      | ( r2_hidden @ X38 @ X42 )
      | ( X42
       != ( k1_enumset1 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X38 @ ( k1_enumset1 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X34 != X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X33 @ X35 @ X36 @ X33 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X30: $i] :
      ( ( k5_xboole_0 @ X30 @ k1_xboole_0 )
      = X30 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( X34 = X35 )
      | ( X34 = X36 )
      | ( X34 = X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_enumset1 @ X50 @ X50 @ X51 )
      = ( k2_tarski @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ X42 )
      | ~ ( zip_tseitin_0 @ X43 @ X39 @ X40 @ X41 )
      | ( X42
       != ( k1_enumset1 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X39 @ X40 @ X41 )
      | ~ ( r2_hidden @ X43 @ ( k1_enumset1 @ X41 @ X40 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( X34 = X35 )
      | ( X34 = X36 )
      | ( X34 = X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ k1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['27'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('63',plain,(
    ! [X30: $i] :
      ( ( k5_xboole_0 @ X30 @ k1_xboole_0 )
      = X30 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61','64'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('68',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20','67'])).

thf('69',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['22','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MVukGSYmHx
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.04/5.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.04/5.29  % Solved by: fo/fo7.sh
% 5.04/5.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.04/5.29  % done 4931 iterations in 4.849s
% 5.04/5.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.04/5.29  % SZS output start Refutation
% 5.04/5.29  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.04/5.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 5.04/5.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.04/5.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.04/5.29  thf(sk_A_type, type, sk_A: $i).
% 5.04/5.29  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.04/5.29  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.04/5.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.04/5.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.04/5.29  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.04/5.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.04/5.29  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.04/5.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.04/5.29  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.04/5.29  thf(t67_zfmisc_1, conjecture,
% 5.04/5.29    (![A:$i,B:$i]:
% 5.04/5.29     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 5.04/5.29       ( ~( r2_hidden @ A @ B ) ) ))).
% 5.04/5.29  thf(zf_stmt_0, negated_conjecture,
% 5.04/5.29    (~( ![A:$i,B:$i]:
% 5.04/5.29        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 5.04/5.29          ( ~( r2_hidden @ A @ B ) ) ) )),
% 5.04/5.29    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 5.04/5.29  thf('0', plain,
% 5.04/5.29      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 5.04/5.29        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 5.04/5.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.29  thf('1', plain,
% 5.04/5.29      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 5.04/5.29      inference('split', [status(esa)], ['0'])).
% 5.04/5.29  thf('2', plain,
% 5.04/5.29      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 5.04/5.29       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 5.04/5.29      inference('split', [status(esa)], ['0'])).
% 5.04/5.29  thf('3', plain,
% 5.04/5.29      (((r2_hidden @ sk_A @ sk_B_1)
% 5.04/5.29        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 5.04/5.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.29  thf('4', plain,
% 5.04/5.29      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 5.04/5.29      inference('split', [status(esa)], ['3'])).
% 5.04/5.29  thf('5', plain,
% 5.04/5.29      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 5.04/5.29         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 5.04/5.29      inference('split', [status(esa)], ['0'])).
% 5.04/5.29  thf(t79_xboole_1, axiom,
% 5.04/5.29    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 5.04/5.29  thf('6', plain,
% 5.04/5.29      (![X31 : $i, X32 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X32)),
% 5.04/5.29      inference('cnf', [status(esa)], [t79_xboole_1])).
% 5.04/5.29  thf('7', plain,
% 5.04/5.29      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 5.04/5.29         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 5.04/5.29      inference('sup+', [status(thm)], ['5', '6'])).
% 5.04/5.29  thf(t69_enumset1, axiom,
% 5.04/5.29    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.04/5.29  thf('8', plain, (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 5.04/5.29      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.04/5.29  thf(t70_enumset1, axiom,
% 5.04/5.29    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.04/5.29  thf('9', plain,
% 5.04/5.29      (![X50 : $i, X51 : $i]:
% 5.04/5.29         ((k1_enumset1 @ X50 @ X50 @ X51) = (k2_tarski @ X50 @ X51))),
% 5.04/5.29      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.04/5.29  thf(d1_enumset1, axiom,
% 5.04/5.29    (![A:$i,B:$i,C:$i,D:$i]:
% 5.04/5.29     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 5.04/5.29       ( ![E:$i]:
% 5.04/5.29         ( ( r2_hidden @ E @ D ) <=>
% 5.04/5.29           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 5.04/5.29  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 5.04/5.29  thf(zf_stmt_2, axiom,
% 5.04/5.29    (![E:$i,C:$i,B:$i,A:$i]:
% 5.04/5.29     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 5.04/5.29       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 5.04/5.29  thf(zf_stmt_3, axiom,
% 5.04/5.29    (![A:$i,B:$i,C:$i,D:$i]:
% 5.04/5.29     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 5.04/5.29       ( ![E:$i]:
% 5.04/5.29         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 5.04/5.29  thf('10', plain,
% 5.04/5.29      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 5.04/5.29         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41)
% 5.04/5.29          | (r2_hidden @ X38 @ X42)
% 5.04/5.29          | ((X42) != (k1_enumset1 @ X41 @ X40 @ X39)))),
% 5.04/5.29      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.04/5.29  thf('11', plain,
% 5.04/5.29      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.04/5.29         ((r2_hidden @ X38 @ (k1_enumset1 @ X41 @ X40 @ X39))
% 5.04/5.29          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41))),
% 5.04/5.29      inference('simplify', [status(thm)], ['10'])).
% 5.04/5.29  thf('12', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.29         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 5.04/5.29          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 5.04/5.29      inference('sup+', [status(thm)], ['9', '11'])).
% 5.04/5.29  thf('13', plain,
% 5.04/5.29      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 5.04/5.29         (((X34) != (X33)) | ~ (zip_tseitin_0 @ X34 @ X35 @ X36 @ X33))),
% 5.04/5.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.04/5.29  thf('14', plain,
% 5.04/5.29      (![X33 : $i, X35 : $i, X36 : $i]:
% 5.04/5.29         ~ (zip_tseitin_0 @ X33 @ X35 @ X36 @ X33)),
% 5.04/5.29      inference('simplify', [status(thm)], ['13'])).
% 5.04/5.29  thf('15', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 5.04/5.29      inference('sup-', [status(thm)], ['12', '14'])).
% 5.04/5.29  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.04/5.29      inference('sup+', [status(thm)], ['8', '15'])).
% 5.04/5.29  thf(t3_xboole_0, axiom,
% 5.04/5.29    (![A:$i,B:$i]:
% 5.04/5.29     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 5.04/5.29            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.04/5.29       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.04/5.29            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 5.04/5.29  thf('17', plain,
% 5.04/5.29      (![X15 : $i, X17 : $i, X18 : $i]:
% 5.04/5.29         (~ (r2_hidden @ X17 @ X15)
% 5.04/5.29          | ~ (r2_hidden @ X17 @ X18)
% 5.04/5.29          | ~ (r1_xboole_0 @ X15 @ X18))),
% 5.04/5.29      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.04/5.29  thf('18', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 5.04/5.29      inference('sup-', [status(thm)], ['16', '17'])).
% 5.04/5.29  thf('19', plain,
% 5.04/5.29      ((~ (r2_hidden @ sk_A @ sk_B_1))
% 5.04/5.29         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 5.04/5.29      inference('sup-', [status(thm)], ['7', '18'])).
% 5.04/5.29  thf('20', plain,
% 5.04/5.29      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 5.04/5.29       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 5.04/5.29      inference('sup-', [status(thm)], ['4', '19'])).
% 5.04/5.29  thf('21', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 5.04/5.29      inference('sat_resolution*', [status(thm)], ['2', '20'])).
% 5.04/5.29  thf('22', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 5.04/5.29      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 5.04/5.29  thf(d4_xboole_0, axiom,
% 5.04/5.29    (![A:$i,B:$i,C:$i]:
% 5.04/5.29     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 5.04/5.29       ( ![D:$i]:
% 5.04/5.29         ( ( r2_hidden @ D @ C ) <=>
% 5.04/5.29           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.04/5.29  thf('23', plain,
% 5.04/5.29      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.04/5.29         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.04/5.29          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.04/5.29          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.04/5.29      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.04/5.29  thf(t5_boole, axiom,
% 5.04/5.29    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.04/5.29  thf('24', plain, (![X30 : $i]: ((k5_xboole_0 @ X30 @ k1_xboole_0) = (X30))),
% 5.04/5.29      inference('cnf', [status(esa)], [t5_boole])).
% 5.04/5.29  thf(t1_xboole_0, axiom,
% 5.04/5.29    (![A:$i,B:$i,C:$i]:
% 5.04/5.29     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 5.04/5.29       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 5.04/5.29  thf('25', plain,
% 5.04/5.29      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.04/5.29         (~ (r2_hidden @ X11 @ X12)
% 5.04/5.29          | ~ (r2_hidden @ X11 @ X13)
% 5.04/5.29          | ~ (r2_hidden @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 5.04/5.29      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.04/5.29  thf('26', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (~ (r2_hidden @ X1 @ X0)
% 5.04/5.29          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 5.04/5.29          | ~ (r2_hidden @ X1 @ X0))),
% 5.04/5.29      inference('sup-', [status(thm)], ['24', '25'])).
% 5.04/5.29  thf('27', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 5.04/5.29      inference('simplify', [status(thm)], ['26'])).
% 5.04/5.29  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.04/5.29      inference('condensation', [status(thm)], ['27'])).
% 5.04/5.29  thf('29', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 5.04/5.29          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.04/5.29      inference('sup-', [status(thm)], ['23', '28'])).
% 5.04/5.29  thf('30', plain,
% 5.04/5.29      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.04/5.29         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 5.04/5.29          | ((X34) = (X35))
% 5.04/5.29          | ((X34) = (X36))
% 5.04/5.29          | ((X34) = (X37)))),
% 5.04/5.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.04/5.29  thf('31', plain,
% 5.04/5.29      (![X15 : $i, X16 : $i]:
% 5.04/5.29         ((r1_xboole_0 @ X15 @ X16) | (r2_hidden @ (sk_C @ X16 @ X15) @ X15))),
% 5.04/5.29      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.04/5.29  thf('32', plain,
% 5.04/5.29      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 5.04/5.29      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.04/5.29  thf('33', plain,
% 5.04/5.29      (![X50 : $i, X51 : $i]:
% 5.04/5.29         ((k1_enumset1 @ X50 @ X50 @ X51) = (k2_tarski @ X50 @ X51))),
% 5.04/5.29      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.04/5.29  thf('34', plain,
% 5.04/5.29      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.04/5.29         (~ (r2_hidden @ X43 @ X42)
% 5.04/5.29          | ~ (zip_tseitin_0 @ X43 @ X39 @ X40 @ X41)
% 5.04/5.29          | ((X42) != (k1_enumset1 @ X41 @ X40 @ X39)))),
% 5.04/5.29      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.04/5.29  thf('35', plain,
% 5.04/5.29      (![X39 : $i, X40 : $i, X41 : $i, X43 : $i]:
% 5.04/5.29         (~ (zip_tseitin_0 @ X43 @ X39 @ X40 @ X41)
% 5.04/5.29          | ~ (r2_hidden @ X43 @ (k1_enumset1 @ X41 @ X40 @ X39)))),
% 5.04/5.29      inference('simplify', [status(thm)], ['34'])).
% 5.04/5.29  thf('36', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.29         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 5.04/5.29          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 5.04/5.29      inference('sup-', [status(thm)], ['33', '35'])).
% 5.04/5.29  thf('37', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 5.04/5.29          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 5.04/5.29      inference('sup-', [status(thm)], ['32', '36'])).
% 5.04/5.29  thf('38', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 5.04/5.29          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 5.04/5.29      inference('sup-', [status(thm)], ['31', '37'])).
% 5.04/5.29  thf('39', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 5.04/5.29          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 5.04/5.29          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 5.04/5.29          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 5.04/5.29      inference('sup-', [status(thm)], ['30', '38'])).
% 5.04/5.29  thf('40', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 5.04/5.29          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 5.04/5.29      inference('simplify', [status(thm)], ['39'])).
% 5.04/5.29  thf('41', plain,
% 5.04/5.29      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.04/5.29         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 5.04/5.29          | ((X34) = (X35))
% 5.04/5.29          | ((X34) = (X36))
% 5.04/5.29          | ((X34) = (X37)))),
% 5.04/5.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.04/5.29  thf('42', plain,
% 5.04/5.29      (![X15 : $i, X16 : $i]:
% 5.04/5.29         ((r1_xboole_0 @ X15 @ X16) | (r2_hidden @ (sk_C @ X16 @ X15) @ X16))),
% 5.04/5.29      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.04/5.29  thf('43', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 5.04/5.29          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 5.04/5.29      inference('sup-', [status(thm)], ['32', '36'])).
% 5.04/5.29  thf('44', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 5.04/5.29          | ~ (zip_tseitin_0 @ (sk_C @ (k1_tarski @ X0) @ X1) @ X0 @ X0 @ X0))),
% 5.04/5.29      inference('sup-', [status(thm)], ['42', '43'])).
% 5.04/5.29  thf('45', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 5.04/5.29          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 5.04/5.29          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 5.04/5.29          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 5.04/5.29      inference('sup-', [status(thm)], ['41', '44'])).
% 5.04/5.29  thf('46', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 5.04/5.29          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 5.04/5.29      inference('simplify', [status(thm)], ['45'])).
% 5.04/5.29  thf('47', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (((X0) = (X1))
% 5.04/5.29          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 5.04/5.29          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.04/5.29      inference('sup+', [status(thm)], ['40', '46'])).
% 5.04/5.29  thf('48', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 5.04/5.29      inference('simplify', [status(thm)], ['47'])).
% 5.04/5.29  thf('49', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 5.04/5.29      inference('sup-', [status(thm)], ['16', '17'])).
% 5.04/5.29  thf('50', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.04/5.29      inference('sup-', [status(thm)], ['48', '49'])).
% 5.04/5.29  thf('51', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.04/5.29          | ((sk_D @ k1_xboole_0 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 5.04/5.29      inference('sup-', [status(thm)], ['29', '50'])).
% 5.04/5.29  thf('52', plain,
% 5.04/5.29      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.04/5.29         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.04/5.29          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 5.04/5.29          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.04/5.29      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.04/5.29  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.04/5.29      inference('condensation', [status(thm)], ['27'])).
% 5.04/5.29  thf('54', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.04/5.29          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.04/5.29      inference('sup-', [status(thm)], ['52', '53'])).
% 5.04/5.29  thf('55', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((r2_hidden @ X0 @ X1)
% 5.04/5.29          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.04/5.29          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 5.04/5.29      inference('sup+', [status(thm)], ['51', '54'])).
% 5.04/5.29  thf('56', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.04/5.29          | (r2_hidden @ X0 @ X1))),
% 5.04/5.29      inference('simplify', [status(thm)], ['55'])).
% 5.04/5.29  thf(commutativity_k3_xboole_0, axiom,
% 5.04/5.29    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.04/5.29  thf('57', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.04/5.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.04/5.29  thf(t100_xboole_1, axiom,
% 5.04/5.29    (![A:$i,B:$i]:
% 5.04/5.29     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.04/5.29  thf('58', plain,
% 5.04/5.29      (![X22 : $i, X23 : $i]:
% 5.04/5.29         ((k4_xboole_0 @ X22 @ X23)
% 5.04/5.29           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 5.04/5.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.04/5.29  thf('59', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         ((k4_xboole_0 @ X0 @ X1)
% 5.04/5.29           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.04/5.29      inference('sup+', [status(thm)], ['57', '58'])).
% 5.04/5.29  thf('60', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 5.04/5.29            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 5.04/5.29          | (r2_hidden @ X0 @ X1))),
% 5.04/5.29      inference('sup+', [status(thm)], ['56', '59'])).
% 5.04/5.29  thf(commutativity_k5_xboole_0, axiom,
% 5.04/5.29    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 5.04/5.29  thf('61', plain,
% 5.04/5.29      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 5.04/5.29      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.04/5.29  thf('62', plain,
% 5.04/5.29      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 5.04/5.29      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.04/5.29  thf('63', plain, (![X30 : $i]: ((k5_xboole_0 @ X30 @ k1_xboole_0) = (X30))),
% 5.04/5.29      inference('cnf', [status(esa)], [t5_boole])).
% 5.04/5.29  thf('64', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.04/5.29      inference('sup+', [status(thm)], ['62', '63'])).
% 5.04/5.29  thf('65', plain,
% 5.04/5.29      (![X0 : $i, X1 : $i]:
% 5.04/5.29         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 5.04/5.29          | (r2_hidden @ X0 @ X1))),
% 5.04/5.29      inference('demod', [status(thm)], ['60', '61', '64'])).
% 5.04/5.29  thf('66', plain,
% 5.04/5.29      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 5.04/5.29         <= (~
% 5.04/5.29             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 5.04/5.29      inference('split', [status(esa)], ['3'])).
% 5.04/5.29  thf('67', plain,
% 5.04/5.29      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 5.04/5.29       ((r2_hidden @ sk_A @ sk_B_1))),
% 5.04/5.29      inference('split', [status(esa)], ['3'])).
% 5.04/5.29  thf('68', plain,
% 5.04/5.29      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 5.04/5.29      inference('sat_resolution*', [status(thm)], ['2', '20', '67'])).
% 5.04/5.29  thf('69', plain,
% 5.04/5.29      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 5.04/5.29      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 5.04/5.29  thf('70', plain,
% 5.04/5.29      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 5.04/5.29        | (r2_hidden @ sk_A @ sk_B_1))),
% 5.04/5.29      inference('sup-', [status(thm)], ['65', '69'])).
% 5.04/5.29  thf('71', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 5.04/5.29      inference('simplify', [status(thm)], ['70'])).
% 5.04/5.29  thf('72', plain, ($false), inference('demod', [status(thm)], ['22', '71'])).
% 5.04/5.29  
% 5.04/5.29  % SZS output end Refutation
% 5.04/5.29  
% 5.14/5.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
