%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ym0oKXFDdO

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:34 EST 2020

% Result     : Theorem 4.57s
% Output     : Refutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 537 expanded)
%              Number of leaves         :   37 ( 174 expanded)
%              Depth                    :   18
%              Number of atoms          : 1282 (5213 expanded)
%              Number of equality atoms :  104 ( 332 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_enumset1 @ X61 @ X61 @ X62 )
      = ( k2_tarski @ X61 @ X62 ) ) ),
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

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 )
      | ( r2_hidden @ X35 @ X39 )
      | ( X39
       != ( k1_enumset1 @ X38 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X35 @ ( k1_enumset1 @ X38 @ X37 @ X36 ) )
      | ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X31 != X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ~ ( zip_tseitin_0 @ X30 @ X32 @ X33 @ X30 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

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
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('32',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('34',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_tarski @ X29 @ X28 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('40',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','30','45','46','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('50',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_tarski @ X29 @ X28 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X88: $i,X89: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X88 @ X89 ) )
      = ( k2_xboole_0 @ X88 @ X89 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X88: $i,X89: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X88 @ X89 ) )
      = ( k2_xboole_0 @ X88 @ X89 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('55',plain,(
    ! [X90: $i,X91: $i,X92: $i] :
      ( ( r2_hidden @ X90 @ X91 )
      | ( r1_xboole_0 @ ( k2_tarski @ X90 @ X92 ) @ X91 )
      | ( r2_hidden @ X92 @ X91 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['58','64'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('67',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','30','45','46'])).

thf('68',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('71',plain,(
    ! [X60: $i] :
      ( ( k2_tarski @ X60 @ X60 )
      = ( k1_tarski @ X60 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('72',plain,(
    ! [X90: $i,X91: $i,X92: $i] :
      ( ( r2_hidden @ X90 @ X91 )
      | ( r1_xboole_0 @ ( k2_tarski @ X90 @ X92 ) @ X91 )
      | ( r2_hidden @ X92 @ X91 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('84',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('87',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('88',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('90',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('91',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('92',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('93',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('95',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('96',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('103',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','104'])).

thf('106',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('107',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('109',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('111',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('113',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
      = sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X60: $i] :
      ( ( k2_tarski @ X60 @ X60 )
      = ( k1_tarski @ X60 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','30'])).

thf('119',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['117','118'])).

thf('120',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(clc,[status(thm)],['70','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['49','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ym0oKXFDdO
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.57/4.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.57/4.81  % Solved by: fo/fo7.sh
% 4.57/4.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.57/4.81  % done 4902 iterations in 4.343s
% 4.57/4.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.57/4.81  % SZS output start Refutation
% 4.57/4.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.57/4.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.57/4.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 4.57/4.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.57/4.81  thf(sk_B_type, type, sk_B: $i).
% 4.57/4.81  thf(sk_A_type, type, sk_A: $i).
% 4.57/4.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.57/4.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.57/4.81  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.57/4.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.57/4.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.57/4.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.57/4.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.57/4.81  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.57/4.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.57/4.81  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.57/4.81  thf(t72_zfmisc_1, conjecture,
% 4.57/4.81    (![A:$i,B:$i,C:$i]:
% 4.57/4.81     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 4.57/4.81       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 4.57/4.81  thf(zf_stmt_0, negated_conjecture,
% 4.57/4.81    (~( ![A:$i,B:$i,C:$i]:
% 4.57/4.81        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 4.57/4.81          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 4.57/4.81    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 4.57/4.81  thf('0', plain,
% 4.57/4.81      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 4.57/4.81        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81            = (k2_tarski @ sk_A @ sk_B)))),
% 4.57/4.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.81  thf('1', plain,
% 4.57/4.81      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 4.57/4.81      inference('split', [status(esa)], ['0'])).
% 4.57/4.81  thf('2', plain,
% 4.57/4.81      ((~ (r2_hidden @ sk_A @ sk_C_1)
% 4.57/4.81        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81            = (k2_tarski @ sk_A @ sk_B)))),
% 4.57/4.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.81  thf('3', plain,
% 4.57/4.81      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 4.57/4.81       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81          = (k2_tarski @ sk_A @ sk_B)))),
% 4.57/4.81      inference('split', [status(esa)], ['2'])).
% 4.57/4.81  thf(t70_enumset1, axiom,
% 4.57/4.81    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.57/4.81  thf('4', plain,
% 4.57/4.81      (![X61 : $i, X62 : $i]:
% 4.57/4.81         ((k1_enumset1 @ X61 @ X61 @ X62) = (k2_tarski @ X61 @ X62))),
% 4.57/4.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.57/4.81  thf(d1_enumset1, axiom,
% 4.57/4.81    (![A:$i,B:$i,C:$i,D:$i]:
% 4.57/4.81     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.57/4.81       ( ![E:$i]:
% 4.57/4.81         ( ( r2_hidden @ E @ D ) <=>
% 4.57/4.81           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 4.57/4.81  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 4.57/4.81  thf(zf_stmt_2, axiom,
% 4.57/4.81    (![E:$i,C:$i,B:$i,A:$i]:
% 4.57/4.81     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 4.57/4.81       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 4.57/4.81  thf(zf_stmt_3, axiom,
% 4.57/4.81    (![A:$i,B:$i,C:$i,D:$i]:
% 4.57/4.81     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.57/4.81       ( ![E:$i]:
% 4.57/4.81         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 4.57/4.81  thf('5', plain,
% 4.57/4.81      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 4.57/4.81         ((zip_tseitin_0 @ X35 @ X36 @ X37 @ X38)
% 4.57/4.81          | (r2_hidden @ X35 @ X39)
% 4.57/4.81          | ((X39) != (k1_enumset1 @ X38 @ X37 @ X36)))),
% 4.57/4.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.57/4.81  thf('6', plain,
% 4.57/4.81      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 4.57/4.81         ((r2_hidden @ X35 @ (k1_enumset1 @ X38 @ X37 @ X36))
% 4.57/4.81          | (zip_tseitin_0 @ X35 @ X36 @ X37 @ X38))),
% 4.57/4.81      inference('simplify', [status(thm)], ['5'])).
% 4.57/4.81  thf('7', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.57/4.81          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 4.57/4.81      inference('sup+', [status(thm)], ['4', '6'])).
% 4.57/4.81  thf('8', plain,
% 4.57/4.81      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 4.57/4.81         (((X31) != (X30)) | ~ (zip_tseitin_0 @ X31 @ X32 @ X33 @ X30))),
% 4.57/4.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.57/4.81  thf('9', plain,
% 4.57/4.81      (![X30 : $i, X32 : $i, X33 : $i]:
% 4.57/4.81         ~ (zip_tseitin_0 @ X30 @ X32 @ X33 @ X30)),
% 4.57/4.81      inference('simplify', [status(thm)], ['8'])).
% 4.57/4.81  thf('10', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 4.57/4.81      inference('sup-', [status(thm)], ['7', '9'])).
% 4.57/4.81  thf('11', plain,
% 4.57/4.81      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81          = (k2_tarski @ sk_A @ sk_B)))
% 4.57/4.81         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))))),
% 4.57/4.81      inference('split', [status(esa)], ['2'])).
% 4.57/4.81  thf(t79_xboole_1, axiom,
% 4.57/4.81    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.57/4.81  thf('12', plain,
% 4.57/4.81      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 4.57/4.81      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.57/4.81  thf('13', plain,
% 4.57/4.81      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 4.57/4.81         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))))),
% 4.57/4.81      inference('sup+', [status(thm)], ['11', '12'])).
% 4.57/4.81  thf(t88_xboole_1, axiom,
% 4.57/4.81    (![A:$i,B:$i]:
% 4.57/4.81     ( ( r1_xboole_0 @ A @ B ) =>
% 4.57/4.81       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 4.57/4.81  thf('14', plain,
% 4.57/4.81      (![X20 : $i, X21 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21) = (X20))
% 4.57/4.81          | ~ (r1_xboole_0 @ X20 @ X21))),
% 4.57/4.81      inference('cnf', [status(esa)], [t88_xboole_1])).
% 4.57/4.81  thf('15', plain,
% 4.57/4.81      ((((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ 
% 4.57/4.81          sk_C_1) = (k2_tarski @ sk_A @ sk_B)))
% 4.57/4.81         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))))),
% 4.57/4.81      inference('sup-', [status(thm)], ['13', '14'])).
% 4.57/4.81  thf('16', plain,
% 4.57/4.81      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 4.57/4.81      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.57/4.81  thf(t3_xboole_0, axiom,
% 4.57/4.81    (![A:$i,B:$i]:
% 4.57/4.81     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 4.57/4.81            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.57/4.81       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.57/4.81            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 4.57/4.81  thf('17', plain,
% 4.57/4.81      (![X4 : $i, X5 : $i]:
% 4.57/4.81         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 4.57/4.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.57/4.81  thf('18', plain,
% 4.57/4.81      (![X4 : $i, X5 : $i]:
% 4.57/4.81         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 4.57/4.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.57/4.81  thf('19', plain,
% 4.57/4.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.57/4.81         (~ (r2_hidden @ X6 @ X4)
% 4.57/4.81          | ~ (r2_hidden @ X6 @ X7)
% 4.57/4.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.57/4.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.57/4.81  thf('20', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         ((r1_xboole_0 @ X1 @ X0)
% 4.57/4.81          | ~ (r1_xboole_0 @ X0 @ X2)
% 4.57/4.81          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 4.57/4.81      inference('sup-', [status(thm)], ['18', '19'])).
% 4.57/4.81  thf('21', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((r1_xboole_0 @ X0 @ X1)
% 4.57/4.81          | ~ (r1_xboole_0 @ X1 @ X0)
% 4.57/4.81          | (r1_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('sup-', [status(thm)], ['17', '20'])).
% 4.57/4.81  thf('22', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('simplify', [status(thm)], ['21'])).
% 4.57/4.81  thf('23', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.57/4.81      inference('sup-', [status(thm)], ['16', '22'])).
% 4.57/4.81  thf('24', plain,
% 4.57/4.81      (((r2_hidden @ sk_B @ sk_C_1)
% 4.57/4.81        | (r2_hidden @ sk_A @ sk_C_1)
% 4.57/4.81        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81            != (k2_tarski @ sk_A @ sk_B)))),
% 4.57/4.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.81  thf('25', plain,
% 4.57/4.81      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('split', [status(esa)], ['24'])).
% 4.57/4.81  thf('26', plain,
% 4.57/4.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.57/4.81         (~ (r2_hidden @ X6 @ X4)
% 4.57/4.81          | ~ (r2_hidden @ X6 @ X7)
% 4.57/4.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.57/4.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.57/4.81  thf('27', plain,
% 4.57/4.81      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 4.57/4.81         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['25', '26'])).
% 4.57/4.81  thf('28', plain,
% 4.57/4.81      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 4.57/4.81         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['23', '27'])).
% 4.57/4.81  thf('29', plain,
% 4.57/4.81      ((~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B)))
% 4.57/4.81         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))) & 
% 4.57/4.81             ((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['15', '28'])).
% 4.57/4.81  thf('30', plain,
% 4.57/4.81      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 4.57/4.81       ~
% 4.57/4.81       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81          = (k2_tarski @ sk_A @ sk_B)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['10', '29'])).
% 4.57/4.81  thf('31', plain,
% 4.57/4.81      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 4.57/4.81      inference('split', [status(esa)], ['24'])).
% 4.57/4.81  thf('32', plain,
% 4.57/4.81      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 4.57/4.81         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))))),
% 4.57/4.81      inference('sup+', [status(thm)], ['11', '12'])).
% 4.57/4.81  thf('33', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('simplify', [status(thm)], ['21'])).
% 4.57/4.81  thf('34', plain,
% 4.57/4.81      (((r1_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 4.57/4.81         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))))),
% 4.57/4.81      inference('sup-', [status(thm)], ['32', '33'])).
% 4.57/4.81  thf('35', plain,
% 4.57/4.81      (![X20 : $i, X21 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21) = (X20))
% 4.57/4.81          | ~ (r1_xboole_0 @ X20 @ X21))),
% 4.57/4.81      inference('cnf', [status(esa)], [t88_xboole_1])).
% 4.57/4.81  thf('36', plain,
% 4.57/4.81      ((((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 4.57/4.81          (k2_tarski @ sk_A @ sk_B)) = (sk_C_1)))
% 4.57/4.81         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))))),
% 4.57/4.81      inference('sup-', [status(thm)], ['34', '35'])).
% 4.57/4.81  thf(commutativity_k2_tarski, axiom,
% 4.57/4.81    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.57/4.81  thf('37', plain,
% 4.57/4.81      (![X28 : $i, X29 : $i]:
% 4.57/4.81         ((k2_tarski @ X29 @ X28) = (k2_tarski @ X28 @ X29))),
% 4.57/4.81      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.57/4.81  thf('38', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.57/4.81      inference('sup-', [status(thm)], ['16', '22'])).
% 4.57/4.81  thf('39', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 4.57/4.81      inference('sup-', [status(thm)], ['7', '9'])).
% 4.57/4.81  thf('40', plain,
% 4.57/4.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.57/4.81         (~ (r2_hidden @ X6 @ X4)
% 4.57/4.81          | ~ (r2_hidden @ X6 @ X7)
% 4.57/4.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.57/4.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.57/4.81  thf('41', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 4.57/4.81          | ~ (r2_hidden @ X1 @ X2))),
% 4.57/4.81      inference('sup-', [status(thm)], ['39', '40'])).
% 4.57/4.81  thf('42', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['38', '41'])).
% 4.57/4.81  thf('43', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['37', '42'])).
% 4.57/4.81  thf('44', plain,
% 4.57/4.81      ((~ (r2_hidden @ sk_B @ sk_C_1))
% 4.57/4.81         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))))),
% 4.57/4.81      inference('sup-', [status(thm)], ['36', '43'])).
% 4.57/4.81  thf('45', plain,
% 4.57/4.81      (~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 4.57/4.81       ~
% 4.57/4.81       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81          = (k2_tarski @ sk_A @ sk_B)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['31', '44'])).
% 4.57/4.81  thf('46', plain,
% 4.57/4.81      (~
% 4.57/4.81       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81          = (k2_tarski @ sk_A @ sk_B))) | 
% 4.57/4.81       ((r2_hidden @ sk_B @ sk_C_1)) | ((r2_hidden @ sk_A @ sk_C_1))),
% 4.57/4.81      inference('split', [status(esa)], ['24'])).
% 4.57/4.81  thf('47', plain,
% 4.57/4.81      (~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 4.57/4.81       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81          = (k2_tarski @ sk_A @ sk_B)))),
% 4.57/4.81      inference('split', [status(esa)], ['0'])).
% 4.57/4.81  thf('48', plain, (~ ((r2_hidden @ sk_B @ sk_C_1))),
% 4.57/4.81      inference('sat_resolution*', [status(thm)], ['3', '30', '45', '46', '47'])).
% 4.57/4.81  thf('49', plain, (~ (r2_hidden @ sk_B @ sk_C_1)),
% 4.57/4.81      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 4.57/4.81  thf('50', plain,
% 4.57/4.81      (![X28 : $i, X29 : $i]:
% 4.57/4.81         ((k2_tarski @ X29 @ X28) = (k2_tarski @ X28 @ X29))),
% 4.57/4.81      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.57/4.81  thf(l51_zfmisc_1, axiom,
% 4.57/4.81    (![A:$i,B:$i]:
% 4.57/4.81     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.57/4.81  thf('51', plain,
% 4.57/4.81      (![X88 : $i, X89 : $i]:
% 4.57/4.81         ((k3_tarski @ (k2_tarski @ X88 @ X89)) = (k2_xboole_0 @ X88 @ X89))),
% 4.57/4.81      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.57/4.81  thf('52', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('sup+', [status(thm)], ['50', '51'])).
% 4.57/4.81  thf('53', plain,
% 4.57/4.81      (![X88 : $i, X89 : $i]:
% 4.57/4.81         ((k3_tarski @ (k2_tarski @ X88 @ X89)) = (k2_xboole_0 @ X88 @ X89))),
% 4.57/4.81      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.57/4.81  thf('54', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('sup+', [status(thm)], ['52', '53'])).
% 4.57/4.81  thf(t57_zfmisc_1, axiom,
% 4.57/4.81    (![A:$i,B:$i,C:$i]:
% 4.57/4.81     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 4.57/4.81          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 4.57/4.81  thf('55', plain,
% 4.57/4.81      (![X90 : $i, X91 : $i, X92 : $i]:
% 4.57/4.81         ((r2_hidden @ X90 @ X91)
% 4.57/4.81          | (r1_xboole_0 @ (k2_tarski @ X90 @ X92) @ X91)
% 4.57/4.81          | (r2_hidden @ X92 @ X91))),
% 4.57/4.81      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 4.57/4.81  thf('56', plain,
% 4.57/4.81      (![X20 : $i, X21 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21) = (X20))
% 4.57/4.81          | ~ (r1_xboole_0 @ X20 @ X21))),
% 4.57/4.81      inference('cnf', [status(esa)], [t88_xboole_1])).
% 4.57/4.81  thf('57', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         ((r2_hidden @ X1 @ X0)
% 4.57/4.81          | (r2_hidden @ X2 @ X0)
% 4.57/4.81          | ((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) @ X0)
% 4.57/4.81              = (k2_tarski @ X2 @ X1)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['55', '56'])).
% 4.57/4.81  thf('58', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) @ X2)
% 4.57/4.81            = (k2_tarski @ X1 @ X0))
% 4.57/4.81          | (r2_hidden @ X1 @ X2)
% 4.57/4.81          | (r2_hidden @ X0 @ X2))),
% 4.57/4.81      inference('sup+', [status(thm)], ['54', '57'])).
% 4.57/4.81  thf('59', plain,
% 4.57/4.81      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 4.57/4.81      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.57/4.81  thf('60', plain,
% 4.57/4.81      (![X20 : $i, X21 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21) = (X20))
% 4.57/4.81          | ~ (r1_xboole_0 @ X20 @ X21))),
% 4.57/4.81      inference('cnf', [status(esa)], [t88_xboole_1])).
% 4.57/4.81  thf('61', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 4.57/4.81           = (k4_xboole_0 @ X1 @ X0))),
% 4.57/4.81      inference('sup-', [status(thm)], ['59', '60'])).
% 4.57/4.81  thf('62', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('sup+', [status(thm)], ['52', '53'])).
% 4.57/4.81  thf(t39_xboole_1, axiom,
% 4.57/4.81    (![A:$i,B:$i]:
% 4.57/4.81     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.57/4.81  thf('63', plain,
% 4.57/4.81      (![X11 : $i, X12 : $i]:
% 4.57/4.81         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 4.57/4.81           = (k2_xboole_0 @ X11 @ X12))),
% 4.57/4.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.57/4.81  thf('64', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 4.57/4.81           = (k4_xboole_0 @ X1 @ X0))),
% 4.57/4.81      inference('demod', [status(thm)], ['61', '62', '63'])).
% 4.57/4.81  thf('65', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) = (k2_tarski @ X1 @ X0))
% 4.57/4.81          | (r2_hidden @ X1 @ X2)
% 4.57/4.81          | (r2_hidden @ X0 @ X2))),
% 4.57/4.81      inference('demod', [status(thm)], ['58', '64'])).
% 4.57/4.81  thf('66', plain,
% 4.57/4.81      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81          != (k2_tarski @ sk_A @ sk_B)))
% 4.57/4.81         <= (~
% 4.57/4.81             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81                = (k2_tarski @ sk_A @ sk_B))))),
% 4.57/4.81      inference('split', [status(esa)], ['24'])).
% 4.57/4.81  thf('67', plain,
% 4.57/4.81      (~
% 4.57/4.81       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81          = (k2_tarski @ sk_A @ sk_B)))),
% 4.57/4.81      inference('sat_resolution*', [status(thm)], ['3', '30', '45', '46'])).
% 4.57/4.81  thf('68', plain,
% 4.57/4.81      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 4.57/4.81         != (k2_tarski @ sk_A @ sk_B))),
% 4.57/4.81      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 4.57/4.81  thf('69', plain,
% 4.57/4.81      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 4.57/4.81        | (r2_hidden @ sk_B @ sk_C_1)
% 4.57/4.81        | (r2_hidden @ sk_A @ sk_C_1))),
% 4.57/4.81      inference('sup-', [status(thm)], ['65', '68'])).
% 4.57/4.81  thf('70', plain,
% 4.57/4.81      (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_B @ sk_C_1))),
% 4.57/4.81      inference('simplify', [status(thm)], ['69'])).
% 4.57/4.81  thf(t69_enumset1, axiom,
% 4.57/4.81    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.57/4.81  thf('71', plain,
% 4.57/4.81      (![X60 : $i]: ((k2_tarski @ X60 @ X60) = (k1_tarski @ X60))),
% 4.57/4.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.57/4.81  thf('72', plain,
% 4.57/4.81      (![X90 : $i, X91 : $i, X92 : $i]:
% 4.57/4.81         ((r2_hidden @ X90 @ X91)
% 4.57/4.81          | (r1_xboole_0 @ (k2_tarski @ X90 @ X92) @ X91)
% 4.57/4.81          | (r2_hidden @ X92 @ X91))),
% 4.57/4.81      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 4.57/4.81  thf('73', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 4.57/4.81          | (r2_hidden @ X0 @ X1)
% 4.57/4.81          | (r2_hidden @ X0 @ X1))),
% 4.57/4.81      inference('sup+', [status(thm)], ['71', '72'])).
% 4.57/4.81  thf('74', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 4.57/4.81      inference('simplify', [status(thm)], ['73'])).
% 4.57/4.81  thf('75', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('simplify', [status(thm)], ['21'])).
% 4.57/4.81  thf('76', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['74', '75'])).
% 4.57/4.81  thf('77', plain,
% 4.57/4.81      (![X20 : $i, X21 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21) = (X20))
% 4.57/4.81          | ~ (r1_xboole_0 @ X20 @ X21))),
% 4.57/4.81      inference('cnf', [status(esa)], [t88_xboole_1])).
% 4.57/4.81  thf('78', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('sup+', [status(thm)], ['52', '53'])).
% 4.57/4.81  thf('79', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 4.57/4.81           = (k4_xboole_0 @ X1 @ X0))),
% 4.57/4.81      inference('demod', [status(thm)], ['61', '62', '63'])).
% 4.57/4.81  thf('80', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 4.57/4.81           = (k4_xboole_0 @ X1 @ X0))),
% 4.57/4.81      inference('sup+', [status(thm)], ['78', '79'])).
% 4.57/4.81  thf('81', plain,
% 4.57/4.81      (![X20 : $i, X21 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 4.57/4.81      inference('demod', [status(thm)], ['77', '80'])).
% 4.57/4.81  thf('82', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((r2_hidden @ X0 @ X1)
% 4.57/4.81          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['76', '81'])).
% 4.57/4.81  thf('83', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.57/4.81      inference('sup-', [status(thm)], ['16', '22'])).
% 4.57/4.81  thf('84', plain,
% 4.57/4.81      (![X20 : $i, X21 : $i]:
% 4.57/4.81         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 4.57/4.81      inference('demod', [status(thm)], ['77', '80'])).
% 4.57/4.81  thf('85', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 4.57/4.81      inference('sup-', [status(thm)], ['83', '84'])).
% 4.57/4.81  thf(t100_xboole_1, axiom,
% 4.57/4.81    (![A:$i,B:$i]:
% 4.57/4.81     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.57/4.81  thf('86', plain,
% 4.57/4.81      (![X8 : $i, X9 : $i]:
% 4.57/4.81         ((k4_xboole_0 @ X8 @ X9)
% 4.57/4.81           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 4.57/4.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.57/4.81  thf(t92_xboole_1, axiom,
% 4.57/4.81    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 4.57/4.81  thf('87', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 4.57/4.81      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.57/4.81  thf(t91_xboole_1, axiom,
% 4.57/4.81    (![A:$i,B:$i,C:$i]:
% 4.57/4.81     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 4.57/4.81       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 4.57/4.81  thf('88', plain,
% 4.57/4.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.57/4.81         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 4.57/4.81           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 4.57/4.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.57/4.81  thf('89', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.57/4.81           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.57/4.81      inference('sup+', [status(thm)], ['87', '88'])).
% 4.57/4.81  thf(idempotence_k2_xboole_0, axiom,
% 4.57/4.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 4.57/4.81  thf('90', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 4.57/4.81      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 4.57/4.81  thf(t95_xboole_1, axiom,
% 4.57/4.81    (![A:$i,B:$i]:
% 4.57/4.81     ( ( k3_xboole_0 @ A @ B ) =
% 4.57/4.81       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 4.57/4.81  thf('91', plain,
% 4.57/4.81      (![X26 : $i, X27 : $i]:
% 4.57/4.81         ((k3_xboole_0 @ X26 @ X27)
% 4.57/4.81           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 4.57/4.81              (k2_xboole_0 @ X26 @ X27)))),
% 4.57/4.81      inference('cnf', [status(esa)], [t95_xboole_1])).
% 4.57/4.81  thf('92', plain,
% 4.57/4.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.57/4.81         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 4.57/4.81           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 4.57/4.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.57/4.81  thf('93', plain,
% 4.57/4.81      (![X26 : $i, X27 : $i]:
% 4.57/4.81         ((k3_xboole_0 @ X26 @ X27)
% 4.57/4.81           = (k5_xboole_0 @ X26 @ 
% 4.57/4.81              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 4.57/4.81      inference('demod', [status(thm)], ['91', '92'])).
% 4.57/4.81  thf('94', plain,
% 4.57/4.81      (![X0 : $i]:
% 4.57/4.81         ((k3_xboole_0 @ X0 @ X0)
% 4.57/4.81           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 4.57/4.81      inference('sup+', [status(thm)], ['90', '93'])).
% 4.57/4.81  thf(idempotence_k3_xboole_0, axiom,
% 4.57/4.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 4.57/4.81  thf('95', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 4.57/4.81      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 4.57/4.81  thf('96', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 4.57/4.81      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.57/4.81  thf('97', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 4.57/4.81      inference('demod', [status(thm)], ['94', '95', '96'])).
% 4.57/4.81  thf(commutativity_k5_xboole_0, axiom,
% 4.57/4.81    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 4.57/4.81  thf('98', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 4.57/4.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.57/4.81  thf('99', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.57/4.81      inference('sup+', [status(thm)], ['97', '98'])).
% 4.57/4.81  thf('100', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.57/4.81      inference('demod', [status(thm)], ['89', '99'])).
% 4.57/4.81  thf('101', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k3_xboole_0 @ X1 @ X0)
% 4.57/4.81           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.57/4.81      inference('sup+', [status(thm)], ['86', '100'])).
% 4.57/4.81  thf('102', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.57/4.81           = (k5_xboole_0 @ X0 @ X0))),
% 4.57/4.81      inference('sup+', [status(thm)], ['85', '101'])).
% 4.57/4.81  thf('103', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 4.57/4.81      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.57/4.81  thf('104', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.57/4.81      inference('demod', [status(thm)], ['102', '103'])).
% 4.57/4.81  thf('105', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 4.57/4.81          | (r2_hidden @ X1 @ X0))),
% 4.57/4.81      inference('sup+', [status(thm)], ['82', '104'])).
% 4.57/4.81  thf('106', plain,
% 4.57/4.81      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('split', [status(esa)], ['2'])).
% 4.57/4.81  thf('107', plain,
% 4.57/4.81      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (k1_xboole_0)))
% 4.57/4.81         <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['105', '106'])).
% 4.57/4.81  thf('108', plain,
% 4.57/4.81      (![X8 : $i, X9 : $i]:
% 4.57/4.81         ((k4_xboole_0 @ X8 @ X9)
% 4.57/4.81           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 4.57/4.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.57/4.81  thf('109', plain,
% 4.57/4.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1)
% 4.57/4.81          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)))
% 4.57/4.81         <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('sup+', [status(thm)], ['107', '108'])).
% 4.57/4.81  thf('110', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 4.57/4.81      inference('demod', [status(thm)], ['94', '95', '96'])).
% 4.57/4.81  thf('111', plain,
% 4.57/4.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (k1_tarski @ sk_A)))
% 4.57/4.81         <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('demod', [status(thm)], ['109', '110'])).
% 4.57/4.81  thf('112', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 4.57/4.81      inference('sup-', [status(thm)], ['83', '84'])).
% 4.57/4.81  thf('113', plain,
% 4.57/4.81      ((((k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (sk_C_1)))
% 4.57/4.81         <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('sup+', [status(thm)], ['111', '112'])).
% 4.57/4.81  thf('114', plain,
% 4.57/4.81      (![X60 : $i]: ((k2_tarski @ X60 @ X60) = (k1_tarski @ X60))),
% 4.57/4.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.57/4.81  thf('115', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.81         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['38', '41'])).
% 4.57/4.81  thf('116', plain,
% 4.57/4.81      (![X0 : $i, X1 : $i]:
% 4.57/4.81         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['114', '115'])).
% 4.57/4.81  thf('117', plain,
% 4.57/4.81      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 4.57/4.81      inference('sup-', [status(thm)], ['113', '116'])).
% 4.57/4.81  thf('118', plain, (~ ((r2_hidden @ sk_A @ sk_C_1))),
% 4.57/4.81      inference('sat_resolution*', [status(thm)], ['3', '30'])).
% 4.57/4.81  thf('119', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 4.57/4.81      inference('simpl_trail', [status(thm)], ['117', '118'])).
% 4.57/4.81  thf('120', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 4.57/4.81      inference('clc', [status(thm)], ['70', '119'])).
% 4.57/4.81  thf('121', plain, ($false), inference('demod', [status(thm)], ['49', '120'])).
% 4.57/4.81  
% 4.57/4.81  % SZS output end Refutation
% 4.57/4.81  
% 4.57/4.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
