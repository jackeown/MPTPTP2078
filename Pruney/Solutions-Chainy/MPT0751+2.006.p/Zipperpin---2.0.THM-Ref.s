%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fff4ijvTiD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:11 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 179 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   21
%              Number of atoms          :  947 (1878 expanded)
%              Number of equality atoms :   62 ( 152 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X20: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( sk_A
       != ( k1_ordinal1 @ X20 ) )
      | ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) )
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

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('7',plain,(
    ! [X20: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( sk_A
       != ( k1_ordinal1 @ X20 ) )
      | ( v4_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( v3_ordinal1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('10',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('12',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t41_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v4_ordinal1 @ A )
      <=> ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ B @ A )
             => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k1_ordinal1 @ X19 ) @ X18 )
      | ~ ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('14',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_1 ) @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ~ ( v4_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X15 ) @ X14 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('21',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_ordinal1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('26',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('30',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( v3_ordinal1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('33',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_ordinal1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X15 ) @ X14 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ ( k1_ordinal1 @ sk_B_1 ) ) )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_ordinal1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('46',plain,
    ( ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('54',plain,(
    ! [X10: $i] :
      ( X10
     != ( k1_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['28','55'])).

thf('57',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
     != ( k1_ordinal1 @ sk_B_1 ) )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('61',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X18 ) )
      | ( v4_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('62',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X18 ) )
      | ( v4_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('63',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('64',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X18 ) )
      | ( v4_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('65',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ ( sk_B @ X18 ) @ X18 )
      | ( v4_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X15 ) @ X14 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( r1_ordinal1 @ X17 @ X16 )
      | ( r2_hidden @ X17 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_ordinal1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X18 ) ) @ X18 )
      | ( v4_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X20: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( sk_A
       != ( k1_ordinal1 @ X20 ) )
      | ( v3_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) )
   <= ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( sk_A != X0 )
        | ( v4_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) ) )
   <= ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference('simplify_reflect+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference('sup-',[status(thm)],['61','87'])).

thf('89',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ! [X20: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X20 ) )
        | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('93',plain,
    ( ~ ! [X20: $i] :
          ( ( sk_A
           != ( k1_ordinal1 @ X20 ) )
          | ~ ( v3_ordinal1 @ X20 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','59','60','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fff4ijvTiD
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 610 iterations in 0.280s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.74  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.54/0.74  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.54/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.74  thf(t42_ordinal1, conjecture,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.74       ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.54/0.74              ( ![B:$i]:
% 0.54/0.74                ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.54/0.74         ( ~( ( ?[B:$i]:
% 0.54/0.74                ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.54/0.74              ( v4_ordinal1 @ A ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i]:
% 0.54/0.74        ( ( v3_ordinal1 @ A ) =>
% 0.54/0.74          ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.54/0.74                 ( ![B:$i]:
% 0.54/0.74                   ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.54/0.74            ( ~( ( ?[B:$i]:
% 0.54/0.74                   ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.54/0.74                 ( v4_ordinal1 @ A ) ) ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t42_ordinal1])).
% 0.54/0.74  thf('0', plain,
% 0.54/0.74      ((~ (v4_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      (~ ((v4_ordinal1 @ sk_A)) | (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('2', plain,
% 0.54/0.74      (![X20 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X20)
% 0.54/0.74          | ((sk_A) != (k1_ordinal1 @ X20))
% 0.54/0.74          | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      ((![X20 : $i]: (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))) | 
% 0.54/0.74       (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.54/0.74      inference('split', [status(esa)], ['2'])).
% 0.54/0.74  thf('4', plain, ((~ (v4_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_1))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('5', plain, (~ ((v4_ordinal1 @ sk_A)) | ((v3_ordinal1 @ sk_B_1))),
% 0.54/0.74      inference('split', [status(esa)], ['4'])).
% 0.54/0.74  thf(t29_ordinal1, axiom,
% 0.54/0.74    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.54/0.74  thf('6', plain,
% 0.54/0.74      (![X13 : $i]:
% 0.54/0.74         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.54/0.74      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.54/0.74  thf('7', plain,
% 0.54/0.74      (![X20 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X20)
% 0.54/0.74          | ((sk_A) != (k1_ordinal1 @ X20))
% 0.54/0.74          | (v4_ordinal1 @ sk_A))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('8', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 0.54/0.74      inference('split', [status(esa)], ['7'])).
% 0.54/0.74  thf('9', plain, (((v3_ordinal1 @ sk_B_1)) <= (((v3_ordinal1 @ sk_B_1)))),
% 0.54/0.74      inference('split', [status(esa)], ['4'])).
% 0.54/0.74  thf('10', plain,
% 0.54/0.74      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.54/0.74         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.54/0.74  thf('11', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_ordinal1 @ X6))),
% 0.54/0.74      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.54/0.74  thf('12', plain,
% 0.54/0.74      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf(t41_ordinal1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.74       ( ( v4_ordinal1 @ A ) <=>
% 0.54/0.74         ( ![B:$i]:
% 0.54/0.74           ( ( v3_ordinal1 @ B ) =>
% 0.54/0.74             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 0.54/0.74  thf('13', plain,
% 0.54/0.74      (![X18 : $i, X19 : $i]:
% 0.54/0.74         (~ (v4_ordinal1 @ X18)
% 0.54/0.74          | ~ (r2_hidden @ X19 @ X18)
% 0.54/0.74          | (r2_hidden @ (k1_ordinal1 @ X19) @ X18)
% 0.54/0.74          | ~ (v3_ordinal1 @ X19)
% 0.54/0.74          | ~ (v3_ordinal1 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.74  thf('14', plain,
% 0.54/0.74      (((~ (v3_ordinal1 @ sk_A)
% 0.54/0.74         | ~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.74         | (r2_hidden @ (k1_ordinal1 @ sk_B_1) @ sk_A)
% 0.54/0.74         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.74  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('16', plain,
% 0.54/0.74      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.54/0.74         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('17', plain,
% 0.54/0.74      (((~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.74         | (r2_hidden @ sk_A @ sk_A)
% 0.54/0.74         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.54/0.74  thf('18', plain,
% 0.54/0.74      (((~ (v4_ordinal1 @ sk_A) | (r2_hidden @ sk_A @ sk_A)))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['9', '17'])).
% 0.54/0.74  thf('19', plain,
% 0.54/0.74      (((r2_hidden @ sk_A @ sk_A))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.74             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.74             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['8', '18'])).
% 0.54/0.74  thf(t33_ordinal1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.74           ( ( r2_hidden @ A @ B ) <=>
% 0.54/0.74             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      (![X14 : $i, X15 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X14)
% 0.54/0.74          | ~ (r2_hidden @ X15 @ X14)
% 0.54/0.74          | (r1_ordinal1 @ (k1_ordinal1 @ X15) @ X14)
% 0.54/0.74          | ~ (v3_ordinal1 @ X15))),
% 0.54/0.74      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      (((~ (v3_ordinal1 @ sk_A)
% 0.54/0.74         | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.54/0.74         | ~ (v3_ordinal1 @ sk_A)))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.74             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.74             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.74  thf('22', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('24', plain,
% 0.54/0.74      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.74             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.74             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.54/0.74  thf(redefinition_r1_ordinal1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.54/0.74       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      (![X4 : $i, X5 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X4)
% 0.54/0.74          | ~ (v3_ordinal1 @ X5)
% 0.54/0.74          | (r1_tarski @ X4 @ X5)
% 0.54/0.74          | ~ (r1_ordinal1 @ X4 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.54/0.74  thf('26', plain,
% 0.54/0.74      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.54/0.74         | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.74         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.74             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.74             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.74  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('28', plain,
% 0.54/0.74      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.54/0.74         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.74             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.74             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.54/0.74  thf('29', plain,
% 0.54/0.74      (![X13 : $i]:
% 0.54/0.74         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.54/0.74      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.54/0.74  thf('30', plain, (((v3_ordinal1 @ sk_B_1)) <= (((v3_ordinal1 @ sk_B_1)))),
% 0.54/0.74      inference('split', [status(esa)], ['4'])).
% 0.54/0.74  thf('31', plain,
% 0.54/0.74      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.54/0.74         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('32', plain,
% 0.54/0.74      (![X13 : $i]:
% 0.54/0.74         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.54/0.74      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.54/0.74  thf('33', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_ordinal1 @ X6))),
% 0.54/0.74      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.54/0.74  thf(t13_ordinal1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.54/0.74       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (![X8 : $i, X9 : $i]:
% 0.54/0.74         ((r2_hidden @ X8 @ (k1_ordinal1 @ X9)) | ~ (r2_hidden @ X8 @ X9))),
% 0.54/0.74      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.54/0.74  thf('35', plain,
% 0.54/0.74      (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('36', plain,
% 0.54/0.74      (![X14 : $i, X15 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X14)
% 0.54/0.74          | ~ (r2_hidden @ X15 @ X14)
% 0.54/0.74          | (r1_ordinal1 @ (k1_ordinal1 @ X15) @ X14)
% 0.54/0.74          | ~ (v3_ordinal1 @ X15))),
% 0.54/0.74      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.54/0.74  thf('37', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ 
% 0.54/0.74             (k1_ordinal1 @ (k1_ordinal1 @ X0)))
% 0.54/0.74          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (k1_ordinal1 @ X0))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.74  thf('38', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.54/0.74          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ 
% 0.54/0.74             (k1_ordinal1 @ (k1_ordinal1 @ X0)))
% 0.54/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['32', '37'])).
% 0.54/0.74  thf('39', plain,
% 0.54/0.74      (![X13 : $i]:
% 0.54/0.74         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.54/0.74      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.54/0.74  thf('40', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ 
% 0.54/0.74             (k1_ordinal1 @ (k1_ordinal1 @ X0))))),
% 0.54/0.74      inference('clc', [status(thm)], ['38', '39'])).
% 0.54/0.74  thf('41', plain,
% 0.54/0.74      ((((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ (k1_ordinal1 @ sk_B_1)))
% 0.54/0.74         | ~ (v3_ordinal1 @ sk_B_1))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup+', [status(thm)], ['31', '40'])).
% 0.54/0.74  thf('42', plain,
% 0.54/0.74      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.54/0.74         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('43', plain,
% 0.54/0.74      ((((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)) | ~ (v3_ordinal1 @ sk_B_1)))
% 0.54/0.74         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('demod', [status(thm)], ['41', '42'])).
% 0.54/0.74  thf('44', plain,
% 0.54/0.74      (((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['30', '43'])).
% 0.54/0.74  thf('45', plain,
% 0.54/0.74      (![X4 : $i, X5 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X4)
% 0.54/0.74          | ~ (v3_ordinal1 @ X5)
% 0.54/0.74          | (r1_tarski @ X4 @ X5)
% 0.54/0.74          | ~ (r1_ordinal1 @ X4 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.54/0.74  thf('46', plain,
% 0.54/0.74      ((((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.54/0.74         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.54/0.74         | ~ (v3_ordinal1 @ sk_A)))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.74  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('48', plain,
% 0.54/0.74      ((((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.54/0.74         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('demod', [status(thm)], ['46', '47'])).
% 0.54/0.74  thf('49', plain,
% 0.54/0.74      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['29', '48'])).
% 0.54/0.74  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('51', plain,
% 0.54/0.74      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.74  thf(d10_xboole_0, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.74  thf('52', plain,
% 0.54/0.74      (![X0 : $i, X2 : $i]:
% 0.54/0.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.74  thf('53', plain,
% 0.54/0.74      (((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.54/0.74         | ((k1_ordinal1 @ sk_A) = (sk_A))))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['51', '52'])).
% 0.54/0.74  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.54/0.74  thf('54', plain, (![X10 : $i]: ((X10) != (k1_ordinal1 @ X10))),
% 0.54/0.74      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.54/0.74  thf('55', plain,
% 0.54/0.74      ((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.54/0.74  thf('56', plain,
% 0.54/0.74      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.74             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.74             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('clc', [status(thm)], ['28', '55'])).
% 0.54/0.74  thf('57', plain,
% 0.54/0.74      ((~ (v3_ordinal1 @ sk_A))
% 0.54/0.74         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.74             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.74             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['6', '56'])).
% 0.54/0.74  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('59', plain,
% 0.54/0.74      (~ ((v4_ordinal1 @ sk_A)) | ~ (((sk_A) = (k1_ordinal1 @ sk_B_1))) | 
% 0.54/0.74       ~ ((v3_ordinal1 @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.54/0.74  thf('60', plain,
% 0.54/0.74      ((![X20 : $i]: (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))) | 
% 0.54/0.74       ((v4_ordinal1 @ sk_A))),
% 0.54/0.74      inference('split', [status(esa)], ['7'])).
% 0.54/0.74  thf('61', plain,
% 0.54/0.74      (![X18 : $i]:
% 0.54/0.74         ((v3_ordinal1 @ (sk_B @ X18))
% 0.54/0.74          | (v4_ordinal1 @ X18)
% 0.54/0.74          | ~ (v3_ordinal1 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.74  thf('62', plain,
% 0.54/0.74      (![X18 : $i]:
% 0.54/0.74         ((v3_ordinal1 @ (sk_B @ X18))
% 0.54/0.74          | (v4_ordinal1 @ X18)
% 0.54/0.74          | ~ (v3_ordinal1 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.74  thf('63', plain,
% 0.54/0.74      (![X13 : $i]:
% 0.54/0.74         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.54/0.74      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.54/0.74  thf('64', plain,
% 0.54/0.74      (![X18 : $i]:
% 0.54/0.74         ((v3_ordinal1 @ (sk_B @ X18))
% 0.54/0.74          | (v4_ordinal1 @ X18)
% 0.54/0.74          | ~ (v3_ordinal1 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.74  thf('65', plain,
% 0.54/0.74      (![X18 : $i]:
% 0.54/0.74         ((r2_hidden @ (sk_B @ X18) @ X18)
% 0.54/0.74          | (v4_ordinal1 @ X18)
% 0.54/0.74          | ~ (v3_ordinal1 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.74  thf('66', plain,
% 0.54/0.74      (![X14 : $i, X15 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X14)
% 0.54/0.74          | ~ (r2_hidden @ X15 @ X14)
% 0.54/0.74          | (r1_ordinal1 @ (k1_ordinal1 @ X15) @ X14)
% 0.54/0.74          | ~ (v3_ordinal1 @ X15))),
% 0.54/0.74      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.54/0.74  thf('67', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.54/0.74          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.74  thf('68', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['67'])).
% 0.54/0.74  thf('69', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['64', '68'])).
% 0.54/0.74  thf('70', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['69'])).
% 0.54/0.74  thf(t34_ordinal1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.74           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.54/0.74             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.54/0.74  thf('71', plain,
% 0.54/0.74      (![X16 : $i, X17 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X16)
% 0.54/0.74          | ~ (r1_ordinal1 @ X17 @ X16)
% 0.54/0.74          | (r2_hidden @ X17 @ (k1_ordinal1 @ X16))
% 0.54/0.74          | ~ (v3_ordinal1 @ X17))),
% 0.54/0.74      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.54/0.74  thf('72', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.54/0.74          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.54/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['70', '71'])).
% 0.54/0.74  thf('73', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.54/0.74          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['72'])).
% 0.54/0.74  thf('74', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.54/0.74          | ~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['63', '73'])).
% 0.54/0.74  thf('75', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['62', '74'])).
% 0.54/0.74  thf('76', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['75'])).
% 0.54/0.74  thf('77', plain,
% 0.54/0.74      (![X7 : $i, X8 : $i]:
% 0.54/0.74         (((X8) = (X7))
% 0.54/0.74          | (r2_hidden @ X8 @ X7)
% 0.54/0.74          | ~ (r2_hidden @ X8 @ (k1_ordinal1 @ X7)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.54/0.74  thf('78', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.54/0.74          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['76', '77'])).
% 0.54/0.74  thf('79', plain,
% 0.54/0.74      (![X18 : $i]:
% 0.54/0.74         (~ (r2_hidden @ (k1_ordinal1 @ (sk_B @ X18)) @ X18)
% 0.54/0.74          | (v4_ordinal1 @ X18)
% 0.54/0.74          | ~ (v3_ordinal1 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.74  thf('80', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0)
% 0.54/0.74          | ~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['78', '79'])).
% 0.54/0.74  thf('81', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X0)
% 0.54/0.74          | (v4_ordinal1 @ X0)
% 0.54/0.74          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['80'])).
% 0.54/0.74  thf('82', plain,
% 0.54/0.74      (![X20 : $i]:
% 0.54/0.74         (~ (v3_ordinal1 @ X20)
% 0.54/0.74          | ((sk_A) != (k1_ordinal1 @ X20))
% 0.54/0.74          | (v3_ordinal1 @ sk_B_1))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('83', plain,
% 0.54/0.74      ((![X20 : $i]: (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20)))
% 0.54/0.74         <= ((![X20 : $i]:
% 0.54/0.74                (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))))),
% 0.54/0.74      inference('split', [status(esa)], ['82'])).
% 0.54/0.74  thf('84', plain,
% 0.54/0.74      ((![X0 : $i]:
% 0.54/0.74          (((sk_A) != (X0))
% 0.54/0.74           | (v4_ordinal1 @ X0)
% 0.54/0.74           | ~ (v3_ordinal1 @ X0)
% 0.54/0.74           | ~ (v3_ordinal1 @ (sk_B @ X0))))
% 0.54/0.74         <= ((![X20 : $i]:
% 0.54/0.74                (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['81', '83'])).
% 0.54/0.74  thf('85', plain,
% 0.54/0.74      (((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.54/0.74         | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.74         | (v4_ordinal1 @ sk_A)))
% 0.54/0.74         <= ((![X20 : $i]:
% 0.54/0.74                (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['84'])).
% 0.54/0.74  thf('86', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('87', plain,
% 0.54/0.74      (((~ (v3_ordinal1 @ (sk_B @ sk_A)) | (v4_ordinal1 @ sk_A)))
% 0.54/0.74         <= ((![X20 : $i]:
% 0.54/0.74                (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))))),
% 0.54/0.74      inference('simplify_reflect+', [status(thm)], ['85', '86'])).
% 0.54/0.74  thf('88', plain,
% 0.54/0.74      (((~ (v3_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.54/0.74         <= ((![X20 : $i]:
% 0.54/0.74                (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['61', '87'])).
% 0.54/0.74  thf('89', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('90', plain,
% 0.54/0.74      ((((v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.54/0.74         <= ((![X20 : $i]:
% 0.54/0.74                (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))))),
% 0.54/0.74      inference('demod', [status(thm)], ['88', '89'])).
% 0.54/0.74  thf('91', plain,
% 0.54/0.74      (((v4_ordinal1 @ sk_A))
% 0.54/0.74         <= ((![X20 : $i]:
% 0.54/0.74                (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['90'])).
% 0.54/0.74  thf('92', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 0.54/0.74      inference('split', [status(esa)], ['4'])).
% 0.54/0.74  thf('93', plain,
% 0.54/0.74      (~
% 0.54/0.74       (![X20 : $i]: (((sk_A) != (k1_ordinal1 @ X20)) | ~ (v3_ordinal1 @ X20))) | 
% 0.54/0.74       ((v4_ordinal1 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['91', '92'])).
% 0.54/0.74  thf('94', plain, ($false),
% 0.54/0.74      inference('sat_resolution*', [status(thm)],
% 0.54/0.74                ['1', '3', '5', '59', '60', '93'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
