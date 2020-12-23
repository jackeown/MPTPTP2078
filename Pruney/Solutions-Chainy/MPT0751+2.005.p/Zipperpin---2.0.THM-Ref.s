%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yq4blHWcDo

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:11 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 182 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   21
%              Number of atoms          :  942 (1939 expanded)
%              Number of equality atoms :   65 ( 164 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

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
    ! [X19: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ( sk_A
       != ( k1_ordinal1 @ X19 ) )
      | ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) )
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
    ! [X12: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('7',plain,(
    ! [X19: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ( sk_A
       != ( k1_ordinal1 @ X19 ) )
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

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_ordinal1 @ X10 ) )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('12',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_ordinal1 @ X10 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf(t41_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v4_ordinal1 @ A )
      <=> ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ B @ A )
             => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_ordinal1 @ X17 )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ( r2_hidden @ ( k1_ordinal1 @ X18 ) @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('15',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_1 ) @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ~ ( v4_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X14 ) @ X13 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('22',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('27',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('31',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( v3_ordinal1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('33',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_ordinal1 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('35',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X14 ) @ X13 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('37',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_1 ) @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('45',plain,
    ( ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('53',plain,(
    ! [X11: $i] :
      ( X11
     != ( k1_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['29','54'])).

thf('56',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','55'])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
     != ( k1_ordinal1 @ sk_B_1 ) )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('60',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X17 ) )
      | ( v4_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('61',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X17 ) )
      | ( v4_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('62',plain,(
    ! [X12: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('63',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X17 ) )
      | ( v4_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('64',plain,(
    ! [X17: $i] :
      ( ( r2_hidden @ ( sk_B @ X17 ) @ X17 )
      | ( v4_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X14 ) @ X13 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('70',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( r1_ordinal1 @ X16 @ X15 )
      | ( r2_hidden @ X16 @ ( k1_ordinal1 @ X15 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( k1_ordinal1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X17 ) ) @ X17 )
      | ( v4_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X19: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ( sk_A
       != ( k1_ordinal1 @ X19 ) )
      | ( v3_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) )
   <= ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( sk_A != X0 )
        | ( v4_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) ) )
   <= ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference('simplify_reflect+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference('sup-',[status(thm)],['60','86'])).

thf('88',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ! [X19: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X19 ) )
        | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('92',plain,
    ( ~ ! [X19: $i] :
          ( ( sk_A
           != ( k1_ordinal1 @ X19 ) )
          | ~ ( v3_ordinal1 @ X19 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','58','59','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yq4blHWcDo
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:57:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 1124 iterations in 0.619s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.06  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.84/1.06  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.84/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.06  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.84/1.06  thf(t42_ordinal1, conjecture,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( v3_ordinal1 @ A ) =>
% 0.84/1.06       ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.84/1.06              ( ![B:$i]:
% 0.84/1.06                ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.84/1.06         ( ~( ( ?[B:$i]:
% 0.84/1.06                ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.84/1.06              ( v4_ordinal1 @ A ) ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.06    (~( ![A:$i]:
% 0.84/1.06        ( ( v3_ordinal1 @ A ) =>
% 0.84/1.06          ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.84/1.06                 ( ![B:$i]:
% 0.84/1.06                   ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.84/1.06            ( ~( ( ?[B:$i]:
% 0.84/1.06                   ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.84/1.06                 ( v4_ordinal1 @ A ) ) ) ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t42_ordinal1])).
% 0.84/1.06  thf('0', plain,
% 0.84/1.06      ((~ (v4_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('1', plain,
% 0.84/1.06      (~ ((v4_ordinal1 @ sk_A)) | (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf('2', plain,
% 0.84/1.06      (![X19 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X19)
% 0.84/1.06          | ((sk_A) != (k1_ordinal1 @ X19))
% 0.84/1.06          | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('3', plain,
% 0.84/1.06      ((![X19 : $i]: (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))) | 
% 0.84/1.06       (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.84/1.06      inference('split', [status(esa)], ['2'])).
% 0.84/1.06  thf('4', plain, ((~ (v4_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_1))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('5', plain, (~ ((v4_ordinal1 @ sk_A)) | ((v3_ordinal1 @ sk_B_1))),
% 0.84/1.06      inference('split', [status(esa)], ['4'])).
% 0.84/1.06  thf(t29_ordinal1, axiom,
% 0.84/1.06    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.84/1.06  thf('6', plain,
% 0.84/1.06      (![X12 : $i]:
% 0.84/1.06         ((v3_ordinal1 @ (k1_ordinal1 @ X12)) | ~ (v3_ordinal1 @ X12))),
% 0.84/1.06      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.84/1.06  thf('7', plain,
% 0.84/1.06      (![X19 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X19)
% 0.84/1.06          | ((sk_A) != (k1_ordinal1 @ X19))
% 0.84/1.06          | (v4_ordinal1 @ sk_A))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('8', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['7'])).
% 0.84/1.06  thf('9', plain, (((v3_ordinal1 @ sk_B_1)) <= (((v3_ordinal1 @ sk_B_1)))),
% 0.84/1.06      inference('split', [status(esa)], ['4'])).
% 0.84/1.06  thf('10', plain,
% 0.84/1.06      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.84/1.06         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf(t13_ordinal1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.84/1.06       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.84/1.06  thf('11', plain,
% 0.84/1.06      (![X9 : $i, X10 : $i]:
% 0.84/1.06         ((r2_hidden @ X9 @ (k1_ordinal1 @ X10)) | ((X9) != (X10)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.84/1.06  thf('12', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_ordinal1 @ X10))),
% 0.84/1.06      inference('simplify', [status(thm)], ['11'])).
% 0.84/1.06  thf('13', plain,
% 0.84/1.06      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup+', [status(thm)], ['10', '12'])).
% 0.84/1.06  thf(t41_ordinal1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( v3_ordinal1 @ A ) =>
% 0.84/1.06       ( ( v4_ordinal1 @ A ) <=>
% 0.84/1.06         ( ![B:$i]:
% 0.84/1.06           ( ( v3_ordinal1 @ B ) =>
% 0.84/1.06             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 0.84/1.06  thf('14', plain,
% 0.84/1.06      (![X17 : $i, X18 : $i]:
% 0.84/1.06         (~ (v4_ordinal1 @ X17)
% 0.84/1.06          | ~ (r2_hidden @ X18 @ X17)
% 0.84/1.06          | (r2_hidden @ (k1_ordinal1 @ X18) @ X17)
% 0.84/1.06          | ~ (v3_ordinal1 @ X18)
% 0.84/1.06          | ~ (v3_ordinal1 @ X17))),
% 0.84/1.06      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.84/1.06  thf('15', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ sk_A)
% 0.84/1.06         | ~ (v3_ordinal1 @ sk_B_1)
% 0.84/1.06         | (r2_hidden @ (k1_ordinal1 @ sk_B_1) @ sk_A)
% 0.84/1.06         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['13', '14'])).
% 0.84/1.06  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('17', plain,
% 0.84/1.06      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.84/1.06         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf('18', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ sk_B_1)
% 0.84/1.06         | (r2_hidden @ sk_A @ sk_A)
% 0.84/1.06         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.84/1.06  thf('19', plain,
% 0.84/1.06      (((~ (v4_ordinal1 @ sk_A) | (r2_hidden @ sk_A @ sk_A)))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['9', '18'])).
% 0.84/1.06  thf('20', plain,
% 0.84/1.06      (((r2_hidden @ sk_A @ sk_A))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.84/1.06             ((v4_ordinal1 @ sk_A)) & 
% 0.84/1.06             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['8', '19'])).
% 0.84/1.06  thf(t33_ordinal1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( v3_ordinal1 @ A ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( v3_ordinal1 @ B ) =>
% 0.84/1.06           ( ( r2_hidden @ A @ B ) <=>
% 0.84/1.06             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      (![X13 : $i, X14 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X13)
% 0.84/1.06          | ~ (r2_hidden @ X14 @ X13)
% 0.84/1.06          | (r1_ordinal1 @ (k1_ordinal1 @ X14) @ X13)
% 0.84/1.06          | ~ (v3_ordinal1 @ X14))),
% 0.84/1.06      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.84/1.06  thf('22', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ sk_A)
% 0.84/1.06         | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.84/1.06         | ~ (v3_ordinal1 @ sk_A)))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.84/1.06             ((v4_ordinal1 @ sk_A)) & 
% 0.84/1.06             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.06  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('25', plain,
% 0.84/1.06      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.84/1.06             ((v4_ordinal1 @ sk_A)) & 
% 0.84/1.06             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.84/1.06  thf(redefinition_r1_ordinal1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.84/1.06       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.84/1.06  thf('26', plain,
% 0.84/1.06      (![X6 : $i, X7 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X6)
% 0.84/1.06          | ~ (v3_ordinal1 @ X7)
% 0.84/1.06          | (r1_tarski @ X6 @ X7)
% 0.84/1.06          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.84/1.06  thf('27', plain,
% 0.84/1.06      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.84/1.06         | ~ (v3_ordinal1 @ sk_A)
% 0.84/1.06         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.84/1.06             ((v4_ordinal1 @ sk_A)) & 
% 0.84/1.06             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['25', '26'])).
% 0.84/1.06  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('29', plain,
% 0.84/1.06      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.84/1.06         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.84/1.06             ((v4_ordinal1 @ sk_A)) & 
% 0.84/1.06             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('demod', [status(thm)], ['27', '28'])).
% 0.84/1.06  thf('30', plain,
% 0.84/1.06      (![X12 : $i]:
% 0.84/1.06         ((v3_ordinal1 @ (k1_ordinal1 @ X12)) | ~ (v3_ordinal1 @ X12))),
% 0.84/1.06      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.84/1.06  thf('31', plain, (((v3_ordinal1 @ sk_B_1)) <= (((v3_ordinal1 @ sk_B_1)))),
% 0.84/1.06      inference('split', [status(esa)], ['4'])).
% 0.84/1.06  thf('32', plain,
% 0.84/1.06      (![X12 : $i]:
% 0.84/1.06         ((v3_ordinal1 @ (k1_ordinal1 @ X12)) | ~ (v3_ordinal1 @ X12))),
% 0.84/1.06      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.84/1.06  thf('33', plain,
% 0.84/1.06      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup+', [status(thm)], ['10', '12'])).
% 0.84/1.06  thf('34', plain,
% 0.84/1.06      (![X9 : $i, X10 : $i]:
% 0.84/1.06         ((r2_hidden @ X9 @ (k1_ordinal1 @ X10)) | ~ (r2_hidden @ X9 @ X10))),
% 0.84/1.06      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.84/1.06  thf('35', plain,
% 0.84/1.06      (((r2_hidden @ sk_B_1 @ (k1_ordinal1 @ sk_A)))
% 0.84/1.06         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.06  thf('36', plain,
% 0.84/1.06      (![X13 : $i, X14 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X13)
% 0.84/1.06          | ~ (r2_hidden @ X14 @ X13)
% 0.84/1.06          | (r1_ordinal1 @ (k1_ordinal1 @ X14) @ X13)
% 0.84/1.06          | ~ (v3_ordinal1 @ X14))),
% 0.84/1.06      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.84/1.06  thf('37', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ sk_B_1)
% 0.84/1.06         | (r1_ordinal1 @ (k1_ordinal1 @ sk_B_1) @ (k1_ordinal1 @ sk_A))
% 0.84/1.06         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.84/1.06         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('38', plain,
% 0.84/1.06      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.84/1.06         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf('39', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ sk_B_1)
% 0.84/1.06         | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.84/1.06         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.84/1.06         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.84/1.06  thf('40', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ sk_A)
% 0.84/1.06         | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.84/1.06         | ~ (v3_ordinal1 @ sk_B_1))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['32', '39'])).
% 0.84/1.06  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('42', plain,
% 0.84/1.06      ((((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)) | ~ (v3_ordinal1 @ sk_B_1)))
% 0.84/1.06         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('demod', [status(thm)], ['40', '41'])).
% 0.84/1.06  thf('43', plain,
% 0.84/1.06      (((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['31', '42'])).
% 0.84/1.06  thf('44', plain,
% 0.84/1.06      (![X6 : $i, X7 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X6)
% 0.84/1.06          | ~ (v3_ordinal1 @ X7)
% 0.84/1.06          | (r1_tarski @ X6 @ X7)
% 0.84/1.06          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.84/1.06  thf('45', plain,
% 0.84/1.06      ((((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.84/1.06         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.84/1.06         | ~ (v3_ordinal1 @ sk_A)))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['43', '44'])).
% 0.84/1.06  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('47', plain,
% 0.84/1.06      ((((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.84/1.06         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('demod', [status(thm)], ['45', '46'])).
% 0.84/1.06  thf('48', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['30', '47'])).
% 0.84/1.06  thf('49', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('50', plain,
% 0.84/1.06      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('demod', [status(thm)], ['48', '49'])).
% 0.84/1.06  thf(d10_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.06  thf('51', plain,
% 0.84/1.06      (![X0 : $i, X2 : $i]:
% 0.84/1.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.84/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.06  thf('52', plain,
% 0.84/1.06      (((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.84/1.06         | ((k1_ordinal1 @ sk_A) = (sk_A))))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['50', '51'])).
% 0.84/1.06  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.84/1.06  thf('53', plain, (![X11 : $i]: ((X11) != (k1_ordinal1 @ X11))),
% 0.84/1.06      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.84/1.06  thf('54', plain,
% 0.84/1.06      ((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.84/1.06  thf('55', plain,
% 0.84/1.06      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.84/1.06             ((v4_ordinal1 @ sk_A)) & 
% 0.84/1.06             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('clc', [status(thm)], ['29', '54'])).
% 0.84/1.06  thf('56', plain,
% 0.84/1.06      ((~ (v3_ordinal1 @ sk_A))
% 0.84/1.06         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.84/1.06             ((v4_ordinal1 @ sk_A)) & 
% 0.84/1.06             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['6', '55'])).
% 0.84/1.06  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('58', plain,
% 0.84/1.06      (~ ((v4_ordinal1 @ sk_A)) | ~ (((sk_A) = (k1_ordinal1 @ sk_B_1))) | 
% 0.84/1.06       ~ ((v3_ordinal1 @ sk_B_1))),
% 0.84/1.06      inference('demod', [status(thm)], ['56', '57'])).
% 0.84/1.06  thf('59', plain,
% 0.84/1.06      ((![X19 : $i]: (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))) | 
% 0.84/1.06       ((v4_ordinal1 @ sk_A))),
% 0.84/1.06      inference('split', [status(esa)], ['7'])).
% 0.84/1.06  thf('60', plain,
% 0.84/1.06      (![X17 : $i]:
% 0.84/1.06         ((v3_ordinal1 @ (sk_B @ X17))
% 0.84/1.06          | (v4_ordinal1 @ X17)
% 0.84/1.06          | ~ (v3_ordinal1 @ X17))),
% 0.84/1.06      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.84/1.06  thf('61', plain,
% 0.84/1.06      (![X17 : $i]:
% 0.84/1.06         ((v3_ordinal1 @ (sk_B @ X17))
% 0.84/1.06          | (v4_ordinal1 @ X17)
% 0.84/1.06          | ~ (v3_ordinal1 @ X17))),
% 0.84/1.06      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.84/1.06  thf('62', plain,
% 0.84/1.06      (![X12 : $i]:
% 0.84/1.06         ((v3_ordinal1 @ (k1_ordinal1 @ X12)) | ~ (v3_ordinal1 @ X12))),
% 0.84/1.06      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.84/1.06  thf('63', plain,
% 0.84/1.06      (![X17 : $i]:
% 0.84/1.06         ((v3_ordinal1 @ (sk_B @ X17))
% 0.84/1.06          | (v4_ordinal1 @ X17)
% 0.84/1.06          | ~ (v3_ordinal1 @ X17))),
% 0.84/1.06      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.84/1.06  thf('64', plain,
% 0.84/1.06      (![X17 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_B @ X17) @ X17)
% 0.84/1.06          | (v4_ordinal1 @ X17)
% 0.84/1.06          | ~ (v3_ordinal1 @ X17))),
% 0.84/1.06      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.84/1.06  thf('65', plain,
% 0.84/1.06      (![X13 : $i, X14 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X13)
% 0.84/1.06          | ~ (r2_hidden @ X14 @ X13)
% 0.84/1.06          | (r1_ordinal1 @ (k1_ordinal1 @ X14) @ X13)
% 0.84/1.06          | ~ (v3_ordinal1 @ X14))),
% 0.84/1.06      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.84/1.06  thf('66', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.84/1.06          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['64', '65'])).
% 0.84/1.06  thf('67', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['66'])).
% 0.84/1.06  thf('68', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['63', '67'])).
% 0.84/1.06  thf('69', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['68'])).
% 0.84/1.06  thf(t34_ordinal1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( v3_ordinal1 @ A ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( v3_ordinal1 @ B ) =>
% 0.84/1.06           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.84/1.06             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.84/1.06  thf('70', plain,
% 0.84/1.06      (![X15 : $i, X16 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X15)
% 0.84/1.06          | ~ (r1_ordinal1 @ X16 @ X15)
% 0.84/1.06          | (r2_hidden @ X16 @ (k1_ordinal1 @ X15))
% 0.84/1.06          | ~ (v3_ordinal1 @ X16))),
% 0.84/1.06      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.84/1.06  thf('71', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.84/1.06          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.84/1.06          | ~ (v3_ordinal1 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['69', '70'])).
% 0.84/1.06  thf('72', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.84/1.06          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['71'])).
% 0.84/1.06  thf('73', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.84/1.06          | ~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['62', '72'])).
% 0.84/1.06  thf('74', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['61', '73'])).
% 0.84/1.06  thf('75', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['74'])).
% 0.84/1.06  thf('76', plain,
% 0.84/1.06      (![X8 : $i, X9 : $i]:
% 0.84/1.06         (((X9) = (X8))
% 0.84/1.06          | (r2_hidden @ X9 @ X8)
% 0.84/1.06          | ~ (r2_hidden @ X9 @ (k1_ordinal1 @ X8)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.84/1.06  thf('77', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.84/1.06          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['75', '76'])).
% 0.84/1.06  thf('78', plain,
% 0.84/1.06      (![X17 : $i]:
% 0.84/1.06         (~ (r2_hidden @ (k1_ordinal1 @ (sk_B @ X17)) @ X17)
% 0.84/1.06          | (v4_ordinal1 @ X17)
% 0.84/1.06          | ~ (v3_ordinal1 @ X17))),
% 0.84/1.06      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.84/1.06  thf('79', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0)
% 0.84/1.06          | ~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['77', '78'])).
% 0.84/1.06  thf('80', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X0)
% 0.84/1.06          | (v4_ordinal1 @ X0)
% 0.84/1.06          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['79'])).
% 0.84/1.06  thf('81', plain,
% 0.84/1.06      (![X19 : $i]:
% 0.84/1.06         (~ (v3_ordinal1 @ X19)
% 0.84/1.06          | ((sk_A) != (k1_ordinal1 @ X19))
% 0.84/1.06          | (v3_ordinal1 @ sk_B_1))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('82', plain,
% 0.84/1.06      ((![X19 : $i]: (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19)))
% 0.84/1.06         <= ((![X19 : $i]:
% 0.84/1.06                (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))))),
% 0.84/1.06      inference('split', [status(esa)], ['81'])).
% 0.84/1.06  thf('83', plain,
% 0.84/1.06      ((![X0 : $i]:
% 0.84/1.06          (((sk_A) != (X0))
% 0.84/1.06           | (v4_ordinal1 @ X0)
% 0.84/1.06           | ~ (v3_ordinal1 @ X0)
% 0.84/1.06           | ~ (v3_ordinal1 @ (sk_B @ X0))))
% 0.84/1.06         <= ((![X19 : $i]:
% 0.84/1.06                (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['80', '82'])).
% 0.84/1.06  thf('84', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.84/1.06         | ~ (v3_ordinal1 @ sk_A)
% 0.84/1.06         | (v4_ordinal1 @ sk_A)))
% 0.84/1.06         <= ((![X19 : $i]:
% 0.84/1.06                (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))))),
% 0.84/1.06      inference('simplify', [status(thm)], ['83'])).
% 0.84/1.06  thf('85', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('86', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ (sk_B @ sk_A)) | (v4_ordinal1 @ sk_A)))
% 0.84/1.06         <= ((![X19 : $i]:
% 0.84/1.06                (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))))),
% 0.84/1.06      inference('simplify_reflect+', [status(thm)], ['84', '85'])).
% 0.84/1.06  thf('87', plain,
% 0.84/1.06      (((~ (v3_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.84/1.06         <= ((![X19 : $i]:
% 0.84/1.06                (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['60', '86'])).
% 0.84/1.06  thf('88', plain, ((v3_ordinal1 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('89', plain,
% 0.84/1.06      ((((v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.84/1.06         <= ((![X19 : $i]:
% 0.84/1.06                (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))))),
% 0.84/1.06      inference('demod', [status(thm)], ['87', '88'])).
% 0.84/1.06  thf('90', plain,
% 0.84/1.06      (((v4_ordinal1 @ sk_A))
% 0.84/1.06         <= ((![X19 : $i]:
% 0.84/1.06                (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))))),
% 0.84/1.06      inference('simplify', [status(thm)], ['89'])).
% 0.84/1.06  thf('91', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['4'])).
% 0.84/1.06  thf('92', plain,
% 0.84/1.06      (~
% 0.84/1.06       (![X19 : $i]: (((sk_A) != (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))) | 
% 0.84/1.06       ((v4_ordinal1 @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['90', '91'])).
% 0.84/1.06  thf('93', plain, ($false),
% 0.84/1.06      inference('sat_resolution*', [status(thm)],
% 0.84/1.06                ['1', '3', '5', '58', '59', '92'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.84/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
