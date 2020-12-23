%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LXqPs5fYAf

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:15 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 551 expanded)
%              Number of leaves         :   20 ( 164 expanded)
%              Depth                    :   25
%              Number of atoms          : 1087 (4901 expanded)
%              Number of equality atoms :  108 ( 512 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['27'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('54',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X36 ) )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('55',plain,
    ( ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','62'])).

thf('64',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X36 ) )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
     != sk_B_1 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','65'])).

thf('67',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','68'])).

thf('70',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','69'])).

thf('71',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ X37 @ ( k1_tarski @ X38 ) )
        = X37 )
      | ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('72',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('81',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('82',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('86',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','91'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('94',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['27'])).

thf('95',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','68','94'])).

thf('96',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('97',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['92','96'])).

thf('98',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['70','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LXqPs5fYAf
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.64/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.80  % Solved by: fo/fo7.sh
% 0.64/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.80  % done 665 iterations in 0.317s
% 0.64/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.80  % SZS output start Refutation
% 0.64/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.64/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.64/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.64/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.64/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.64/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.64/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.64/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.64/0.80  thf(t67_zfmisc_1, conjecture,
% 0.64/0.80    (![A:$i,B:$i]:
% 0.64/0.80     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.64/0.80       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.64/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.80    (~( ![A:$i,B:$i]:
% 0.64/0.80        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.64/0.80          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.64/0.80    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.64/0.80  thf('0', plain,
% 0.64/0.80      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.64/0.80        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.64/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.80  thf('1', plain,
% 0.64/0.80      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('split', [status(esa)], ['0'])).
% 0.64/0.80  thf('2', plain,
% 0.64/0.80      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.64/0.80       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.64/0.80      inference('split', [status(esa)], ['0'])).
% 0.64/0.80  thf(d10_xboole_0, axiom,
% 0.64/0.80    (![A:$i,B:$i]:
% 0.64/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.64/0.80  thf('3', plain,
% 0.64/0.80      (![X15 : $i, X16 : $i]: ((r1_tarski @ X15 @ X16) | ((X15) != (X16)))),
% 0.64/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.64/0.80  thf('4', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 0.64/0.80      inference('simplify', [status(thm)], ['3'])).
% 0.64/0.80  thf(t28_xboole_1, axiom,
% 0.64/0.80    (![A:$i,B:$i]:
% 0.64/0.80     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.64/0.80  thf('5', plain,
% 0.64/0.80      (![X20 : $i, X21 : $i]:
% 0.64/0.80         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.64/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.64/0.80  thf('6', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.64/0.80  thf(commutativity_k3_xboole_0, axiom,
% 0.64/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.64/0.80  thf('7', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.64/0.80  thf(t100_xboole_1, axiom,
% 0.64/0.80    (![A:$i,B:$i]:
% 0.64/0.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.64/0.80  thf('8', plain,
% 0.64/0.80      (![X18 : $i, X19 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X18 @ X19)
% 0.64/0.80           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.64/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.64/0.80  thf('9', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.64/0.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.64/0.80      inference('sup+', [status(thm)], ['7', '8'])).
% 0.64/0.80  thf('10', plain,
% 0.64/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.64/0.80      inference('sup+', [status(thm)], ['6', '9'])).
% 0.64/0.80  thf(t48_xboole_1, axiom,
% 0.64/0.80    (![A:$i,B:$i]:
% 0.64/0.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.64/0.80  thf('11', plain,
% 0.64/0.80      (![X24 : $i, X25 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.64/0.80           = (k3_xboole_0 @ X24 @ X25))),
% 0.64/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.64/0.80  thf('12', plain,
% 0.64/0.80      (![X0 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.64/0.80           = (k3_xboole_0 @ X0 @ X0))),
% 0.64/0.80      inference('sup+', [status(thm)], ['10', '11'])).
% 0.64/0.80  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.64/0.80  thf('14', plain,
% 0.64/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.64/0.80      inference('demod', [status(thm)], ['12', '13'])).
% 0.64/0.80  thf(t7_xboole_0, axiom,
% 0.64/0.80    (![A:$i]:
% 0.64/0.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.64/0.80          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.64/0.80  thf('15', plain,
% 0.64/0.80      (![X14 : $i]:
% 0.64/0.80         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.64/0.80      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.64/0.80  thf('16', plain,
% 0.64/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.64/0.80      inference('sup+', [status(thm)], ['6', '9'])).
% 0.64/0.80  thf(d5_xboole_0, axiom,
% 0.64/0.80    (![A:$i,B:$i,C:$i]:
% 0.64/0.80     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.64/0.80       ( ![D:$i]:
% 0.64/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.64/0.80           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.64/0.80  thf('17', plain,
% 0.64/0.80      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X12 @ X11)
% 0.64/0.80          | (r2_hidden @ X12 @ X9)
% 0.64/0.80          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.64/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.64/0.80  thf('18', plain,
% 0.64/0.80      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.64/0.80         ((r2_hidden @ X12 @ X9)
% 0.64/0.80          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.64/0.80      inference('simplify', [status(thm)], ['17'])).
% 0.64/0.80  thf('19', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['16', '18'])).
% 0.64/0.80  thf('20', plain,
% 0.64/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.64/0.80      inference('sup+', [status(thm)], ['6', '9'])).
% 0.64/0.80  thf('21', plain,
% 0.64/0.80      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X12 @ X11)
% 0.64/0.80          | ~ (r2_hidden @ X12 @ X10)
% 0.64/0.80          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.64/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.64/0.80  thf('22', plain,
% 0.64/0.80      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X12 @ X10)
% 0.64/0.80          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.64/0.80      inference('simplify', [status(thm)], ['21'])).
% 0.64/0.80  thf('23', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.64/0.80          | ~ (r2_hidden @ X1 @ X0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['20', '22'])).
% 0.64/0.80  thf('24', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.64/0.80      inference('clc', [status(thm)], ['19', '23'])).
% 0.64/0.80  thf('25', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['15', '24'])).
% 0.64/0.80  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.64/0.80      inference('demod', [status(thm)], ['14', '25'])).
% 0.64/0.80  thf('27', plain,
% 0.64/0.80      (((r2_hidden @ sk_A @ sk_B_1)
% 0.64/0.80        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.64/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.80  thf('28', plain,
% 0.64/0.80      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('split', [status(esa)], ['27'])).
% 0.64/0.80  thf('29', plain,
% 0.64/0.80      (![X14 : $i]:
% 0.64/0.80         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.64/0.80      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.64/0.80  thf(t65_zfmisc_1, axiom,
% 0.64/0.80    (![A:$i,B:$i]:
% 0.64/0.80     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.64/0.80       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.64/0.80  thf('30', plain,
% 0.64/0.80      (![X37 : $i, X38 : $i]:
% 0.64/0.80         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 0.64/0.80          | (r2_hidden @ X38 @ X37))),
% 0.64/0.80      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.64/0.80  thf('31', plain,
% 0.64/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('split', [status(esa)], ['0'])).
% 0.64/0.80  thf('32', plain,
% 0.64/0.80      (![X24 : $i, X25 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.64/0.80           = (k3_xboole_0 @ X24 @ X25))),
% 0.64/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.64/0.80  thf('33', plain,
% 0.64/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.64/0.80          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.64/0.80  thf('34', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.64/0.80  thf('35', plain,
% 0.64/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.64/0.80          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('demod', [status(thm)], ['33', '34'])).
% 0.64/0.80  thf('36', plain,
% 0.64/0.80      (((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.64/0.80         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('sup+', [status(thm)], ['30', '35'])).
% 0.64/0.80  thf('37', plain,
% 0.64/0.80      (((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.64/0.80         | (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('sup+', [status(thm)], ['30', '35'])).
% 0.64/0.80  thf('38', plain,
% 0.64/0.80      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('split', [status(esa)], ['27'])).
% 0.64/0.80  thf(d4_xboole_0, axiom,
% 0.64/0.80    (![A:$i,B:$i,C:$i]:
% 0.64/0.80     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.64/0.80       ( ![D:$i]:
% 0.64/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.64/0.80           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.64/0.80  thf('39', plain,
% 0.64/0.80      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X2 @ X3)
% 0.64/0.80          | ~ (r2_hidden @ X2 @ X4)
% 0.64/0.80          | (r2_hidden @ X2 @ X5)
% 0.64/0.80          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.64/0.80      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.64/0.80  thf('40', plain,
% 0.64/0.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.64/0.80         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.64/0.80          | ~ (r2_hidden @ X2 @ X4)
% 0.64/0.80          | ~ (r2_hidden @ X2 @ X3))),
% 0.64/0.80      inference('simplify', [status(thm)], ['39'])).
% 0.64/0.80  thf('41', plain,
% 0.64/0.80      ((![X0 : $i]:
% 0.64/0.80          (~ (r2_hidden @ sk_A @ X0)
% 0.64/0.80           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.64/0.80         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['38', '40'])).
% 0.64/0.80  thf('42', plain,
% 0.64/0.80      (((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.64/0.80         | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['37', '41'])).
% 0.64/0.80  thf('43', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.64/0.80  thf('44', plain,
% 0.64/0.80      (((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.64/0.80         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('demod', [status(thm)], ['42', '43'])).
% 0.64/0.80  thf('45', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.64/0.80  thf('46', plain,
% 0.64/0.80      (![X24 : $i, X25 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.64/0.80           = (k3_xboole_0 @ X24 @ X25))),
% 0.64/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.64/0.80  thf('47', plain,
% 0.64/0.80      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X12 @ X10)
% 0.64/0.80          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.64/0.80      inference('simplify', [status(thm)], ['21'])).
% 0.64/0.80  thf('48', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.64/0.80          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['46', '47'])).
% 0.64/0.80  thf('49', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.64/0.80          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['45', '48'])).
% 0.64/0.80  thf('50', plain,
% 0.64/0.80      (((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.64/0.80         | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['44', '49'])).
% 0.64/0.80  thf('51', plain,
% 0.64/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('split', [status(esa)], ['0'])).
% 0.64/0.80  thf('52', plain,
% 0.64/0.80      (((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.64/0.80         | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('demod', [status(thm)], ['50', '51'])).
% 0.64/0.80  thf('53', plain,
% 0.64/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.64/0.80          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('demod', [status(thm)], ['33', '34'])).
% 0.64/0.80  thf('54', plain,
% 0.64/0.80      (![X36 : $i, X37 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X36 @ X37)
% 0.64/0.80          | ((k4_xboole_0 @ X37 @ (k1_tarski @ X36)) != (X37)))),
% 0.64/0.80      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.64/0.80  thf('55', plain,
% 0.64/0.80      (((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))
% 0.64/0.80         | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.64/0.80  thf('56', plain,
% 0.64/0.80      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('clc', [status(thm)], ['52', '55'])).
% 0.64/0.80  thf('57', plain,
% 0.64/0.80      ((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['36', '56'])).
% 0.64/0.80  thf('58', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.64/0.80          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['45', '48'])).
% 0.64/0.80  thf('59', plain,
% 0.64/0.80      ((![X0 : $i]:
% 0.64/0.80          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.64/0.80           | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['57', '58'])).
% 0.64/0.80  thf('60', plain,
% 0.64/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('split', [status(esa)], ['0'])).
% 0.64/0.80  thf('61', plain,
% 0.64/0.80      ((![X0 : $i]:
% 0.64/0.80          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.64/0.80           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('demod', [status(thm)], ['59', '60'])).
% 0.64/0.80  thf('62', plain,
% 0.64/0.80      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('simplify', [status(thm)], ['61'])).
% 0.64/0.80  thf('63', plain,
% 0.64/0.80      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['29', '62'])).
% 0.64/0.80  thf('64', plain,
% 0.64/0.80      (![X36 : $i, X37 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X36 @ X37)
% 0.64/0.80          | ((k4_xboole_0 @ X37 @ (k1_tarski @ X36)) != (X37)))),
% 0.64/0.80      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.64/0.80  thf('65', plain,
% 0.64/0.80      ((![X0 : $i]:
% 0.64/0.80          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.64/0.80           | ~ (r2_hidden @ sk_A @ X0)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['63', '64'])).
% 0.64/0.80  thf('66', plain,
% 0.64/0.80      ((((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) != (sk_B_1)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['28', '65'])).
% 0.64/0.80  thf('67', plain,
% 0.64/0.80      ((((sk_B_1) != (sk_B_1)))
% 0.64/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.64/0.80             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['26', '66'])).
% 0.64/0.80  thf('68', plain,
% 0.64/0.80      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.64/0.80       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.64/0.80      inference('simplify', [status(thm)], ['67'])).
% 0.64/0.80  thf('69', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.64/0.80      inference('sat_resolution*', [status(thm)], ['2', '68'])).
% 0.64/0.80  thf('70', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.64/0.80      inference('simpl_trail', [status(thm)], ['1', '69'])).
% 0.64/0.80  thf('71', plain,
% 0.64/0.80      (![X37 : $i, X38 : $i]:
% 0.64/0.80         (((k4_xboole_0 @ X37 @ (k1_tarski @ X38)) = (X37))
% 0.64/0.80          | (r2_hidden @ X38 @ X37))),
% 0.64/0.80      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.64/0.80  thf('72', plain,
% 0.64/0.80      (![X24 : $i, X25 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.64/0.80           = (k3_xboole_0 @ X24 @ X25))),
% 0.64/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.64/0.80  thf('73', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.64/0.80          | (r2_hidden @ X1 @ X0))),
% 0.64/0.80      inference('sup+', [status(thm)], ['71', '72'])).
% 0.64/0.80  thf('74', plain,
% 0.64/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.64/0.80      inference('sup+', [status(thm)], ['6', '9'])).
% 0.64/0.80  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['15', '24'])).
% 0.64/0.80  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.64/0.80      inference('demod', [status(thm)], ['74', '75'])).
% 0.64/0.80  thf('77', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.64/0.80          | (r2_hidden @ X1 @ X0))),
% 0.64/0.80      inference('demod', [status(thm)], ['73', '76'])).
% 0.64/0.80  thf('78', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.64/0.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.64/0.80      inference('sup+', [status(thm)], ['7', '8'])).
% 0.64/0.80  thf('79', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.64/0.80            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.64/0.80          | (r2_hidden @ X0 @ X1))),
% 0.64/0.80      inference('sup+', [status(thm)], ['77', '78'])).
% 0.64/0.80  thf('80', plain,
% 0.64/0.80      (![X14 : $i]:
% 0.64/0.80         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.64/0.80      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.64/0.80  thf('81', plain,
% 0.64/0.80      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X6 @ X5)
% 0.64/0.80          | (r2_hidden @ X6 @ X4)
% 0.64/0.80          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.64/0.80      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.64/0.80  thf('82', plain,
% 0.64/0.80      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.64/0.80         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.64/0.80      inference('simplify', [status(thm)], ['81'])).
% 0.64/0.80  thf('83', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.64/0.80          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['80', '82'])).
% 0.64/0.80  thf('84', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.64/0.80      inference('clc', [status(thm)], ['19', '23'])).
% 0.64/0.80  thf('85', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['15', '24'])).
% 0.64/0.80  thf('86', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.64/0.80      inference('demod', [status(thm)], ['84', '85'])).
% 0.64/0.80  thf('87', plain,
% 0.64/0.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['83', '86'])).
% 0.64/0.80  thf('88', plain,
% 0.64/0.80      (![X18 : $i, X19 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X18 @ X19)
% 0.64/0.80           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.64/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.64/0.80  thf('89', plain,
% 0.64/0.80      (![X0 : $i]:
% 0.64/0.80         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.64/0.80      inference('sup+', [status(thm)], ['87', '88'])).
% 0.64/0.80  thf('90', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.64/0.80      inference('demod', [status(thm)], ['14', '25'])).
% 0.64/0.80  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.64/0.80      inference('sup+', [status(thm)], ['89', '90'])).
% 0.64/0.80  thf('92', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.64/0.80          | (r2_hidden @ X0 @ X1))),
% 0.64/0.80      inference('demod', [status(thm)], ['79', '91'])).
% 0.64/0.80  thf('93', plain,
% 0.64/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.64/0.80         <= (~
% 0.64/0.80             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.64/0.80      inference('split', [status(esa)], ['27'])).
% 0.64/0.80  thf('94', plain,
% 0.64/0.80      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.64/0.80       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.64/0.80      inference('split', [status(esa)], ['27'])).
% 0.64/0.80  thf('95', plain,
% 0.64/0.80      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.64/0.80      inference('sat_resolution*', [status(thm)], ['2', '68', '94'])).
% 0.64/0.80  thf('96', plain,
% 0.64/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.64/0.80      inference('simpl_trail', [status(thm)], ['93', '95'])).
% 0.64/0.80  thf('97', plain,
% 0.64/0.80      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.64/0.80        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.64/0.80      inference('sup-', [status(thm)], ['92', '96'])).
% 0.64/0.80  thf('98', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.64/0.80      inference('simplify', [status(thm)], ['97'])).
% 0.64/0.80  thf('99', plain, ($false), inference('demod', [status(thm)], ['70', '98'])).
% 0.64/0.80  
% 0.64/0.80  % SZS output end Refutation
% 0.64/0.80  
% 0.64/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
