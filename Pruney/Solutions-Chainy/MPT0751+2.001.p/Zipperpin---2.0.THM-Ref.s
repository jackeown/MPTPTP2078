%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D4jrXXDyXK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 154 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   26
%              Number of atoms          :  743 (1593 expanded)
%              Number of equality atoms :   45 ( 127 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t42_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( ~ ( v4_ordinal1 @ A )
            & ! [B: $i] :
                ( ( v3_ordinal1 @ B )
               => ( A
                 != ( k1_ordinal1 @ B ) ) ) )
        & ~ ( ? [B: $i] :
                ( ( A
                  = ( k1_ordinal1 @ B ) )
                & ( v3_ordinal1 @ B ) )
            & ( v4_ordinal1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( ~ ( ~ ( v4_ordinal1 @ A )
              & ! [B: $i] :
                  ( ( v3_ordinal1 @ B )
                 => ( A
                   != ( k1_ordinal1 @ B ) ) ) )
          & ~ ( ? [B: $i] :
                  ( ( A
                    = ( k1_ordinal1 @ B ) )
                  & ( v3_ordinal1 @ B ) )
              & ( v4_ordinal1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_ordinal1])).

thf('0',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X16: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( sk_A
       != ( k1_ordinal1 @ X16 ) )
      | ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X16: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( sk_A
       != ( k1_ordinal1 @ X16 ) )
      | ( v4_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( v3_ordinal1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('9',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('11',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t41_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v4_ordinal1 @ A )
      <=> ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ B @ A )
             => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_ordinal1 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ ( k1_ordinal1 @ X15 ) @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('13',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_1 ) @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( ~ ( v4_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('22',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
     != ( k1_ordinal1 @ sk_B_1 ) )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('24',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('25',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X11 ) )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( ( v1_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('30',plain,(
    ! [X11: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X11 ) )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_B @ X14 ) @ X14 )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X13 ) @ X12 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r1_tarski @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( r1_tarski @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r1_tarski @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r1_tarski @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('44',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( r2_xboole_0 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_xboole_0 @ X10 @ X9 )
      | ~ ( v1_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X14 ) ) @ X14 )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X16: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( sk_A
       != ( k1_ordinal1 @ X16 ) )
      | ( v3_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( sk_A != X0 )
        | ~ ( v3_ordinal1 @ X0 )
        | ( v4_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference('simplify_reflect+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference('sup-',[status(thm)],['24','60'])).

thf('62',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('66',plain,
    ( ~ ! [X16: $i] :
          ( ( sk_A
           != ( k1_ordinal1 @ X16 ) )
          | ~ ( v3_ordinal1 @ X16 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','22','23','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D4jrXXDyXK
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 88 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.49  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.21/0.49  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.49  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(t42_ordinal1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49       ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.21/0.49              ( ![B:$i]:
% 0.21/0.49                ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.21/0.49         ( ~( ( ?[B:$i]:
% 0.21/0.49                ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.21/0.49              ( v4_ordinal1 @ A ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49          ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.21/0.49                 ( ![B:$i]:
% 0.21/0.49                   ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.21/0.49            ( ~( ( ?[B:$i]:
% 0.21/0.49                   ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.21/0.49                 ( v4_ordinal1 @ A ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t42_ordinal1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (v4_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (~ ((v4_ordinal1 @ sk_A)) | (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X16 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X16)
% 0.21/0.49          | ((sk_A) != (k1_ordinal1 @ X16))
% 0.21/0.49          | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))) | 
% 0.21/0.49       (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('4', plain, ((~ (v4_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, (~ ((v4_ordinal1 @ sk_A)) | ((v3_ordinal1 @ sk_B_1))),
% 0.21/0.49      inference('split', [status(esa)], ['4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X16 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X16)
% 0.21/0.49          | ((sk_A) != (k1_ordinal1 @ X16))
% 0.21/0.49          | (v4_ordinal1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['6'])).
% 0.21/0.49  thf('8', plain, (((v3_ordinal1 @ sk_B_1)) <= (((v3_ordinal1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['4'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.21/0.49         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.21/0.49  thf('10', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_ordinal1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf(t41_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49       ( ( v4_ordinal1 @ A ) <=>
% 0.21/0.49         ( ![B:$i]:
% 0.21/0.49           ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (v4_ordinal1 @ X14)
% 0.21/0.49          | ~ (r2_hidden @ X15 @ X14)
% 0.21/0.49          | (r2_hidden @ (k1_ordinal1 @ X15) @ X14)
% 0.21/0.49          | ~ (v3_ordinal1 @ X15)
% 0.21/0.49          | ~ (v3_ordinal1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (((~ (v3_ordinal1 @ sk_A)
% 0.21/0.49         | ~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.49         | (r2_hidden @ (k1_ordinal1 @ sk_B_1) @ sk_A)
% 0.21/0.49         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.21/0.49         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (((~ (v3_ordinal1 @ sk_B_1)
% 0.21/0.49         | (r2_hidden @ sk_A @ sk_A)
% 0.21/0.49         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((~ (v4_ordinal1 @ sk_A) | (r2_hidden @ sk_A @ sk_A)))
% 0.21/0.49         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ sk_A))
% 0.21/0.49         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.21/0.49             ((v4_ordinal1 @ sk_A)) & 
% 0.21/0.49             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '17'])).
% 0.21/0.49  thf(antisymmetry_r2_hidden, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_A @ sk_A))
% 0.21/0.49         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.21/0.49             ((v4_ordinal1 @ sk_A)) & 
% 0.21/0.49             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ sk_A))
% 0.21/0.49         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.21/0.49             ((v4_ordinal1 @ sk_A)) & 
% 0.21/0.49             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '17'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (~ ((v4_ordinal1 @ sk_A)) | ~ (((sk_A) = (k1_ordinal1 @ sk_B_1))) | 
% 0.21/0.49       ~ ((v3_ordinal1 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))) | 
% 0.21/0.49       ((v4_ordinal1 @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['6'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X14 : $i]:
% 0.21/0.49         ((v3_ordinal1 @ (sk_B @ X14))
% 0.21/0.49          | (v4_ordinal1 @ X14)
% 0.21/0.49          | ~ (v3_ordinal1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X14 : $i]:
% 0.21/0.49         ((v3_ordinal1 @ (sk_B @ X14))
% 0.21/0.49          | (v4_ordinal1 @ X14)
% 0.21/0.49          | ~ (v3_ordinal1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.21/0.49  thf(t29_ordinal1, axiom,
% 0.21/0.49    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         ((v3_ordinal1 @ (k1_ordinal1 @ X11)) | ~ (v3_ordinal1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.21/0.49  thf(cc1_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.49  thf('27', plain, (![X5 : $i]: ((v1_ordinal1 @ X5) | ~ (v3_ordinal1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v1_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X14 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ (sk_B @ X14))
% 0.21/0.50          | (v4_ordinal1 @ X14)
% 0.21/0.50          | ~ (v3_ordinal1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X11 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ (k1_ordinal1 @ X11)) | ~ (v3_ordinal1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X14 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ (sk_B @ X14))
% 0.21/0.50          | (v4_ordinal1 @ X14)
% 0.21/0.50          | ~ (v3_ordinal1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X14 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_B @ X14) @ X14)
% 0.21/0.50          | (v4_ordinal1 @ X14)
% 0.21/0.50          | ~ (v3_ordinal1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.21/0.50  thf(t33_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50           ( ( r2_hidden @ A @ B ) <=>
% 0.21/0.50             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X12)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X12)
% 0.21/0.50          | (r1_ordinal1 @ (k1_ordinal1 @ X13) @ X12)
% 0.21/0.50          | ~ (v3_ordinal1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.21/0.50          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.50  thf(redefinition_r1_ordinal1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.50       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X6)
% 0.21/0.50          | ~ (v3_ordinal1 @ X7)
% 0.21/0.50          | (r1_tarski @ X6 @ X7)
% 0.21/0.50          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | (r1_tarski @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.21/0.50          | (r1_tarski @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | (r1_tarski @ (k1_ordinal1 @ (sk_B @ X0)) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | (r1_tarski @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.50  thf(d8_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.50       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X2 : $i, X4 : $i]:
% 0.21/0.50         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.21/0.50          | (r2_xboole_0 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf(t21_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X9)
% 0.21/0.50          | (r2_hidden @ X10 @ X9)
% 0.21/0.50          | ~ (r2_xboole_0 @ X10 @ X9)
% 0.21/0.50          | ~ (v1_ordinal1 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | ~ (v1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.21/0.50          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | ~ (v1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.21/0.50          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.21/0.50          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X14 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k1_ordinal1 @ (sk_B @ X14)) @ X14)
% 0.21/0.50          | (v4_ordinal1 @ X14)
% 0.21/0.50          | ~ (v3_ordinal1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (v4_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.21/0.50          | (v4_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X16 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X16)
% 0.21/0.50          | ((sk_A) != (k1_ordinal1 @ X16))
% 0.21/0.50          | (v3_ordinal1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16)))
% 0.21/0.50         <= ((![X16 : $i]:
% 0.21/0.50                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.21/0.50      inference('split', [status(esa)], ['55'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((sk_A) != (X0))
% 0.21/0.50           | ~ (v3_ordinal1 @ X0)
% 0.21/0.50           | (v4_ordinal1 @ X0)
% 0.21/0.50           | ~ (v3_ordinal1 @ (sk_B @ X0))))
% 0.21/0.50         <= ((![X16 : $i]:
% 0.21/0.50                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['54', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.21/0.50         | (v4_ordinal1 @ sk_A)
% 0.21/0.50         | ~ (v3_ordinal1 @ sk_A)))
% 0.21/0.50         <= ((![X16 : $i]:
% 0.21/0.50                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.50  thf('59', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (((~ (v3_ordinal1 @ (sk_B @ sk_A)) | (v4_ordinal1 @ sk_A)))
% 0.21/0.50         <= ((![X16 : $i]:
% 0.21/0.50                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['58', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (((~ (v3_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.21/0.50         <= ((![X16 : $i]:
% 0.21/0.50                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '60'])).
% 0.21/0.50  thf('62', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      ((((v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.21/0.50         <= ((![X16 : $i]:
% 0.21/0.50                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.21/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (((v4_ordinal1 @ sk_A))
% 0.21/0.50         <= ((![X16 : $i]:
% 0.21/0.50                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.50  thf('65', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['4'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (~
% 0.21/0.50       (![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))) | 
% 0.21/0.50       ((v4_ordinal1 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)],
% 0.21/0.50                ['1', '3', '5', '22', '23', '66'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
