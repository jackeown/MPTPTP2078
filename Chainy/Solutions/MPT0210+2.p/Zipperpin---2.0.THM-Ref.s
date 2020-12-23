%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0210+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aXjq9CzSVm

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:49 EST 2020

% Result     : Theorem 19.01s
% Output     : Refutation 19.01s
% Verified   : 
% Statistics : Number of formulae       :   62 (  69 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  423 ( 521 expanded)
%              Number of equality atoms :   53 (  67 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( C @ A ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( X58 @ X59 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( X59 @ X58 ) @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 @ X1 ) )
      | ( ( sk_C_2 @ ( X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( X58 @ X59 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( X59 @ X58 ) @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( X0 @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 @ X1 ) )
      | ( r2_hidden @ ( X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( X1 @ X0 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('12',plain,(
    ! [X264: $i,X265: $i] :
      ( ( k4_xboole_0 @ ( X264 @ ( k3_xboole_0 @ ( X264 @ X265 ) ) ) )
      = ( k4_xboole_0 @ ( X264 @ X265 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( X1 @ o_0_0_xboole_0 ) )
        = ( k4_xboole_0 @ ( X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( r2_hidden @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('15',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ k1_xboole_0 ) )
      = X244 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ ( X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( r2_hidden @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t136_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != B )
        & ( A != C )
        & ( ( k4_xboole_0 @ ( k1_enumset1 @ ( A @ ( B @ C ) ) @ ( k1_tarski @ A ) ) )
         != ( k2_tarski @ ( B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != B )
          & ( A != C )
          & ( ( k4_xboole_0 @ ( k1_enumset1 @ ( A @ ( B @ C ) ) @ ( k1_tarski @ A ) ) )
           != ( k2_tarski @ ( B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t136_enumset1])).

thf('19',plain,(
    ( k4_xboole_0 @ ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) @ ( k1_tarski @ sk_A_2 ) ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_C_6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k1_enumset1 @ ( B @ ( C @ A ) ) ) ) )).

thf('20',plain,(
    ! [X544: $i,X545: $i,X546: $i] :
      ( ( k1_enumset1 @ ( X546 @ ( X544 @ X545 ) ) )
      = ( k1_enumset1 @ ( X544 @ ( X545 @ X546 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('21',plain,(
    ! [X544: $i,X545: $i,X546: $i] :
      ( ( k1_enumset1 @ ( X546 @ ( X544 @ X545 ) ) )
      = ( k1_enumset1 @ ( X544 @ ( X545 @ X546 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('22',plain,(
    ( k4_xboole_0 @ ( k1_enumset1 @ ( sk_B_2 @ ( sk_C_6 @ sk_A_2 ) ) @ ( k1_tarski @ sk_A_2 ) ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_C_6 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ C ) ) ) ) )).

thf('23',plain,(
    ! [X701: $i,X702: $i,X703: $i] :
      ( ( k1_enumset1 @ ( X701 @ ( X702 @ X703 ) ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( X701 @ X702 ) @ ( k1_tarski @ X703 ) ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('24',plain,(
    ! [X246: $i,X247: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X246 @ X247 ) @ X247 ) )
      = ( k4_xboole_0 @ ( X246 @ X247 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k1_enumset1 @ ( X2 @ ( X1 @ X0 ) ) @ ( k1_tarski @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_tarski @ ( X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ ( sk_B_2 @ sk_C_6 ) @ ( k1_tarski @ sk_A_2 ) ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_C_6 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( k2_tarski @ ( sk_B_2 @ sk_C_6 ) )
     != ( k2_tarski @ ( sk_B_2 @ sk_C_6 ) ) )
    | ( r2_hidden @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_6 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('29',plain,(
    ! [X441: $i,X443: $i,X444: $i,X445: $i] :
      ( ~ ( r2_hidden @ ( X445 @ X443 ) )
      | ( X445 = X444 )
      | ( X445 = X441 )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('30',plain,(
    ! [X441: $i,X444: $i,X445: $i] :
      ( ( X445 = X441 )
      | ( X445 = X444 )
      | ~ ( r2_hidden @ ( X445 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A_2 = sk_B_2 )
    | ( sk_A_2 = sk_C_6 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    sk_A_2 != sk_C_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_A_2 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32','33'])).

%------------------------------------------------------------------------------
