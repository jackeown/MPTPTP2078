%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0730+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9MVomEjRTU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 42.59s
% Output     : Refutation 42.59s
% Verified   : 
% Statistics : Number of formulae       :   49 (  76 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  358 ( 617 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_30_type,type,(
    sk_B_30: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_12_type,type,(
    sk_A_12: $i )).

thf(t13_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ ( k1_ordinal1 @ B ) ) )
    <=> ( ( r2_hidden @ ( A @ B ) )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ ( A @ ( k1_ordinal1 @ B ) ) )
      <=> ( ( r2_hidden @ ( A @ B ) )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_ordinal1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) )
    | ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) )
    | ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ ( A @ ( k1_tarski @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3064: $i] :
      ( ( k1_ordinal1 @ X3064 )
      = ( k2_xboole_0 @ ( X3064 @ ( k1_tarski @ X3064 ) ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,
    ( ( sk_A_12 = sk_B_30 )
    | ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) )
    | ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) )
   <= ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X18 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_A_12 @ ( k2_xboole_0 @ ( X0 @ sk_B_30 ) ) ) )
   <= ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_A_12 @ ( k2_xboole_0 @ ( sk_B_30 @ X0 ) ) ) )
   <= ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,
    ( ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) )
   <= ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) )
   <= ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) )
    | ~ ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A_12 != sk_B_30 )
    | ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A_12 != sk_B_30 )
    | ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) )
   <= ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('16',plain,(
    ! [X3064: $i] :
      ( ( k1_ordinal1 @ X3064 )
      = ( k2_xboole_0 @ ( X3064 @ ( k1_tarski @ X3064 ) ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( X21 @ X19 ) )
      | ( r2_hidden @ ( X21 @ X20 ) )
      | ( r2_hidden @ ( X21 @ X18 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('18',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( X21 @ X18 ) )
      | ( r2_hidden @ ( X21 @ X20 ) )
      | ~ ( r2_hidden @ ( X21 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ ( k1_ordinal1 @ X0 ) ) )
      | ( r2_hidden @ ( X1 @ X0 ) )
      | ( r2_hidden @ ( X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( r2_hidden @ ( sk_A_12 @ ( k1_tarski @ sk_B_30 ) ) )
      | ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) )
   <= ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) )
      | ( sk_A_12 = sk_B_30 ) )
   <= ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) )
   <= ~ ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_A_12 = sk_B_30 )
   <= ( ~ ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) )
      & ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A_12 != sk_B_30 )
   <= ( sk_A_12 != sk_B_30 ) ),
    inference(split,[status(esa)],['13'])).

thf('27',plain,
    ( ( sk_A_12 != sk_A_12 )
   <= ( ( sk_A_12 != sk_B_30 )
      & ~ ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) )
      & ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A_12 = sk_B_30 )
    | ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) )
    | ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_A_12 = sk_B_30 )
    | ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) )
    | ( r2_hidden @ ( sk_A_12 @ sk_B_30 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ ( A @ ( k1_ordinal1 @ A ) ) ) )).

thf('30',plain,(
    ! [X3067: $i] :
      ( r2_hidden @ ( X3067 @ ( k1_ordinal1 @ X3067 ) ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('31',plain,
    ( ( sk_A_12 = sk_B_30 )
   <= ( sk_A_12 = sk_B_30 ) ),
    inference(split,[status(esa)],['4'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) )
   <= ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_A_12 ) ) )
   <= ( ~ ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) )
      & ( sk_A_12 = sk_B_30 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A_12 != sk_B_30 )
    | ( r2_hidden @ ( sk_A_12 @ ( k1_ordinal1 @ sk_B_30 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','14','28','29','34'])).

%------------------------------------------------------------------------------
