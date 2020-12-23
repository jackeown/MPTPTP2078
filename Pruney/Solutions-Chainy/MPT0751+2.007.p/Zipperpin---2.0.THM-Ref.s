%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FKUdHYB2Df

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:11 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 182 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   21
%              Number of atoms          :  953 (1919 expanded)
%              Number of equality atoms :   63 ( 156 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf(fc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( v1_xboole_0 @ ( k1_ordinal1 @ A ) )
        & ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('7',plain,(
    ! [X16: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( sk_A
       != ( k1_ordinal1 @ X16 ) )
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
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_ordinal1 @ X8 ) )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('12',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_ordinal1 @ X8 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_ordinal1 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ ( k1_ordinal1 @ X15 ) @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X11 ) @ X10 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_ordinal1 @ X4 @ X5 ) ) ),
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
    ! [X3: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('31',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( v3_ordinal1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('32',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('34',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_ordinal1 @ X8 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_ordinal1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X11 ) @ X10 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ ( k1_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ ( k1_ordinal1 @ sk_B_1 ) ) )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_ordinal1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('47',plain,
    ( ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,
    ( ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('55',plain,(
    ! [X9: $i] :
      ( X9
     != ( k1_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['29','56'])).

thf('58',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ( v3_ordinal1 @ sk_B_1 )
      & ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','57'])).

thf('59',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
     != ( k1_ordinal1 @ sk_B_1 ) )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('62',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('63',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('66',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_B @ X14 ) @ X14 )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X11 ) @ X10 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k1_ordinal1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X14 ) ) @ X14 )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X16: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( sk_A
       != ( k1_ordinal1 @ X16 ) )
      | ( v3_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( sk_A != X0 )
        | ( v4_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference('simplify_reflect+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference('sup-',[status(thm)],['62','88'])).

thf('90',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('94',plain,
    ( ~ ! [X16: $i] :
          ( ( sk_A
           != ( k1_ordinal1 @ X16 ) )
          | ~ ( v3_ordinal1 @ X16 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','60','61','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FKUdHYB2Df
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.72  % Solved by: fo/fo7.sh
% 0.54/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.72  % done 553 iterations in 0.261s
% 0.54/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.72  % SZS output start Refutation
% 0.54/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.72  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.54/0.72  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.54/0.72  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.54/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.72  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.54/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.72  thf(t42_ordinal1, conjecture,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.72       ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.54/0.72              ( ![B:$i]:
% 0.54/0.72                ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.54/0.72         ( ~( ( ?[B:$i]:
% 0.54/0.72                ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.54/0.72              ( v4_ordinal1 @ A ) ) ) ) ))).
% 0.54/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.72    (~( ![A:$i]:
% 0.54/0.72        ( ( v3_ordinal1 @ A ) =>
% 0.54/0.72          ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.54/0.72                 ( ![B:$i]:
% 0.54/0.72                   ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.54/0.72            ( ~( ( ?[B:$i]:
% 0.54/0.72                   ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.54/0.72                 ( v4_ordinal1 @ A ) ) ) ) ) )),
% 0.54/0.72    inference('cnf.neg', [status(esa)], [t42_ordinal1])).
% 0.54/0.72  thf('0', plain,
% 0.54/0.72      ((~ (v4_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('1', plain,
% 0.54/0.72      (~ ((v4_ordinal1 @ sk_A)) | (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.54/0.72      inference('split', [status(esa)], ['0'])).
% 0.54/0.72  thf('2', plain,
% 0.54/0.72      (![X16 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X16)
% 0.54/0.72          | ((sk_A) != (k1_ordinal1 @ X16))
% 0.54/0.72          | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('3', plain,
% 0.54/0.72      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))) | 
% 0.54/0.72       (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.54/0.72      inference('split', [status(esa)], ['2'])).
% 0.54/0.72  thf('4', plain, ((~ (v4_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_1))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('5', plain, (~ ((v4_ordinal1 @ sk_A)) | ((v3_ordinal1 @ sk_B_1))),
% 0.54/0.72      inference('split', [status(esa)], ['4'])).
% 0.54/0.72  thf(fc2_ordinal1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.72       ( ( ~( v1_xboole_0 @ ( k1_ordinal1 @ A ) ) ) & 
% 0.54/0.72         ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ))).
% 0.54/0.72  thf('6', plain,
% 0.54/0.72      (![X3 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X3)) | ~ (v3_ordinal1 @ X3))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.54/0.72  thf('7', plain,
% 0.54/0.72      (![X16 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X16)
% 0.54/0.72          | ((sk_A) != (k1_ordinal1 @ X16))
% 0.54/0.72          | (v4_ordinal1 @ sk_A))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('8', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 0.54/0.72      inference('split', [status(esa)], ['7'])).
% 0.54/0.72  thf('9', plain, (((v3_ordinal1 @ sk_B_1)) <= (((v3_ordinal1 @ sk_B_1)))),
% 0.54/0.72      inference('split', [status(esa)], ['4'])).
% 0.54/0.72  thf('10', plain,
% 0.54/0.72      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.54/0.72         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('split', [status(esa)], ['0'])).
% 0.54/0.72  thf(t13_ordinal1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.54/0.72       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.54/0.72  thf('11', plain,
% 0.54/0.72      (![X7 : $i, X8 : $i]:
% 0.54/0.72         ((r2_hidden @ X7 @ (k1_ordinal1 @ X8)) | ((X7) != (X8)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.54/0.72  thf('12', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_ordinal1 @ X8))),
% 0.54/0.72      inference('simplify', [status(thm)], ['11'])).
% 0.54/0.72  thf('13', plain,
% 0.54/0.72      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup+', [status(thm)], ['10', '12'])).
% 0.54/0.72  thf(t41_ordinal1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.72       ( ( v4_ordinal1 @ A ) <=>
% 0.54/0.72         ( ![B:$i]:
% 0.54/0.72           ( ( v3_ordinal1 @ B ) =>
% 0.54/0.72             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 0.54/0.72  thf('14', plain,
% 0.54/0.72      (![X14 : $i, X15 : $i]:
% 0.54/0.72         (~ (v4_ordinal1 @ X14)
% 0.54/0.72          | ~ (r2_hidden @ X15 @ X14)
% 0.54/0.72          | (r2_hidden @ (k1_ordinal1 @ X15) @ X14)
% 0.54/0.72          | ~ (v3_ordinal1 @ X15)
% 0.54/0.72          | ~ (v3_ordinal1 @ X14))),
% 0.54/0.72      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.72  thf('15', plain,
% 0.54/0.72      (((~ (v3_ordinal1 @ sk_A)
% 0.54/0.72         | ~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.72         | (r2_hidden @ (k1_ordinal1 @ sk_B_1) @ sk_A)
% 0.54/0.72         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.72  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('17', plain,
% 0.54/0.72      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.54/0.72         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('split', [status(esa)], ['0'])).
% 0.54/0.72  thf('18', plain,
% 0.54/0.72      (((~ (v3_ordinal1 @ sk_B_1)
% 0.54/0.72         | (r2_hidden @ sk_A @ sk_A)
% 0.54/0.72         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.54/0.72  thf('19', plain,
% 0.54/0.72      (((~ (v4_ordinal1 @ sk_A) | (r2_hidden @ sk_A @ sk_A)))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['9', '18'])).
% 0.54/0.72  thf('20', plain,
% 0.54/0.72      (((r2_hidden @ sk_A @ sk_A))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.72             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.72             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['8', '19'])).
% 0.54/0.72  thf(t33_ordinal1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.72           ( ( r2_hidden @ A @ B ) <=>
% 0.54/0.72             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.54/0.72  thf('21', plain,
% 0.54/0.72      (![X10 : $i, X11 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X10)
% 0.54/0.72          | ~ (r2_hidden @ X11 @ X10)
% 0.54/0.72          | (r1_ordinal1 @ (k1_ordinal1 @ X11) @ X10)
% 0.54/0.72          | ~ (v3_ordinal1 @ X11))),
% 0.54/0.72      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.54/0.72  thf('22', plain,
% 0.54/0.72      (((~ (v3_ordinal1 @ sk_A)
% 0.54/0.72         | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.54/0.72         | ~ (v3_ordinal1 @ sk_A)))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.72             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.72             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.72  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('25', plain,
% 0.54/0.72      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.72             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.72             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.54/0.72  thf(redefinition_r1_ordinal1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.54/0.72       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.54/0.72  thf('26', plain,
% 0.54/0.72      (![X4 : $i, X5 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X4)
% 0.54/0.72          | ~ (v3_ordinal1 @ X5)
% 0.54/0.72          | (r1_tarski @ X4 @ X5)
% 0.54/0.72          | ~ (r1_ordinal1 @ X4 @ X5))),
% 0.54/0.72      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.54/0.72  thf('27', plain,
% 0.54/0.72      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.54/0.72         | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.72         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.72             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.72             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['25', '26'])).
% 0.54/0.72  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('29', plain,
% 0.54/0.72      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.54/0.72         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.72             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.72             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('demod', [status(thm)], ['27', '28'])).
% 0.54/0.72  thf('30', plain,
% 0.54/0.72      (![X3 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X3)) | ~ (v3_ordinal1 @ X3))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.54/0.72  thf('31', plain, (((v3_ordinal1 @ sk_B_1)) <= (((v3_ordinal1 @ sk_B_1)))),
% 0.54/0.72      inference('split', [status(esa)], ['4'])).
% 0.54/0.72  thf('32', plain,
% 0.54/0.72      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.54/0.72         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('split', [status(esa)], ['0'])).
% 0.54/0.72  thf('33', plain,
% 0.54/0.72      (![X3 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X3)) | ~ (v3_ordinal1 @ X3))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.54/0.72  thf('34', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_ordinal1 @ X8))),
% 0.54/0.72      inference('simplify', [status(thm)], ['11'])).
% 0.54/0.72  thf('35', plain,
% 0.54/0.72      (![X7 : $i, X8 : $i]:
% 0.54/0.72         ((r2_hidden @ X7 @ (k1_ordinal1 @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 0.54/0.72      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.54/0.72  thf('36', plain,
% 0.54/0.72      (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['34', '35'])).
% 0.54/0.72  thf('37', plain,
% 0.54/0.72      (![X10 : $i, X11 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X10)
% 0.54/0.72          | ~ (r2_hidden @ X11 @ X10)
% 0.54/0.72          | (r1_ordinal1 @ (k1_ordinal1 @ X11) @ X10)
% 0.54/0.72          | ~ (v3_ordinal1 @ X11))),
% 0.54/0.72      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.54/0.72  thf('38', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ 
% 0.54/0.72             (k1_ordinal1 @ (k1_ordinal1 @ X0)))
% 0.54/0.72          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (k1_ordinal1 @ X0))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.54/0.72  thf('39', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.54/0.72          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ 
% 0.54/0.72             (k1_ordinal1 @ (k1_ordinal1 @ X0)))
% 0.54/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['33', '38'])).
% 0.54/0.72  thf('40', plain,
% 0.54/0.72      (![X3 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X3)) | ~ (v3_ordinal1 @ X3))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.54/0.72  thf('41', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ 
% 0.54/0.72             (k1_ordinal1 @ (k1_ordinal1 @ X0))))),
% 0.54/0.72      inference('clc', [status(thm)], ['39', '40'])).
% 0.54/0.72  thf('42', plain,
% 0.54/0.72      ((((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ (k1_ordinal1 @ sk_B_1)))
% 0.54/0.72         | ~ (v3_ordinal1 @ sk_B_1))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup+', [status(thm)], ['32', '41'])).
% 0.54/0.72  thf('43', plain,
% 0.54/0.72      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.54/0.72         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('split', [status(esa)], ['0'])).
% 0.54/0.72  thf('44', plain,
% 0.54/0.72      ((((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)) | ~ (v3_ordinal1 @ sk_B_1)))
% 0.54/0.72         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.72  thf('45', plain,
% 0.54/0.72      (((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['31', '44'])).
% 0.54/0.72  thf('46', plain,
% 0.54/0.72      (![X4 : $i, X5 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X4)
% 0.54/0.72          | ~ (v3_ordinal1 @ X5)
% 0.54/0.72          | (r1_tarski @ X4 @ X5)
% 0.54/0.72          | ~ (r1_ordinal1 @ X4 @ X5))),
% 0.54/0.72      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.54/0.72  thf('47', plain,
% 0.54/0.72      ((((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.54/0.72         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.54/0.72         | ~ (v3_ordinal1 @ sk_A)))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['45', '46'])).
% 0.54/0.72  thf('48', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('49', plain,
% 0.54/0.72      ((((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.54/0.72         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('demod', [status(thm)], ['47', '48'])).
% 0.54/0.72  thf('50', plain,
% 0.54/0.72      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['30', '49'])).
% 0.54/0.72  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('52', plain,
% 0.54/0.72      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('demod', [status(thm)], ['50', '51'])).
% 0.54/0.72  thf(d10_xboole_0, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.72  thf('53', plain,
% 0.54/0.72      (![X0 : $i, X2 : $i]:
% 0.54/0.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.72  thf('54', plain,
% 0.54/0.72      (((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.54/0.72         | ((k1_ordinal1 @ sk_A) = (sk_A))))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['52', '53'])).
% 0.54/0.72  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.54/0.72  thf('55', plain, (![X9 : $i]: ((X9) != (k1_ordinal1 @ X9))),
% 0.54/0.72      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.54/0.72  thf('56', plain,
% 0.54/0.72      ((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.54/0.72  thf('57', plain,
% 0.54/0.72      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.72             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.72             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('clc', [status(thm)], ['29', '56'])).
% 0.54/0.72  thf('58', plain,
% 0.54/0.72      ((~ (v3_ordinal1 @ sk_A))
% 0.54/0.72         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.54/0.72             ((v4_ordinal1 @ sk_A)) & 
% 0.54/0.72             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['6', '57'])).
% 0.54/0.72  thf('59', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('60', plain,
% 0.54/0.72      (~ ((v4_ordinal1 @ sk_A)) | ~ (((sk_A) = (k1_ordinal1 @ sk_B_1))) | 
% 0.54/0.72       ~ ((v3_ordinal1 @ sk_B_1))),
% 0.54/0.72      inference('demod', [status(thm)], ['58', '59'])).
% 0.54/0.72  thf('61', plain,
% 0.54/0.72      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))) | 
% 0.54/0.72       ((v4_ordinal1 @ sk_A))),
% 0.54/0.72      inference('split', [status(esa)], ['7'])).
% 0.54/0.72  thf('62', plain,
% 0.54/0.72      (![X14 : $i]:
% 0.54/0.72         ((v3_ordinal1 @ (sk_B @ X14))
% 0.54/0.72          | (v4_ordinal1 @ X14)
% 0.54/0.72          | ~ (v3_ordinal1 @ X14))),
% 0.54/0.72      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.72  thf('63', plain,
% 0.54/0.72      (![X14 : $i]:
% 0.54/0.72         ((v3_ordinal1 @ (sk_B @ X14))
% 0.54/0.72          | (v4_ordinal1 @ X14)
% 0.54/0.72          | ~ (v3_ordinal1 @ X14))),
% 0.54/0.72      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.72  thf('64', plain,
% 0.54/0.72      (![X3 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X3)) | ~ (v3_ordinal1 @ X3))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.54/0.72  thf('65', plain,
% 0.54/0.72      (![X14 : $i]:
% 0.54/0.72         ((v3_ordinal1 @ (sk_B @ X14))
% 0.54/0.72          | (v4_ordinal1 @ X14)
% 0.54/0.72          | ~ (v3_ordinal1 @ X14))),
% 0.54/0.72      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.72  thf('66', plain,
% 0.54/0.72      (![X14 : $i]:
% 0.54/0.72         ((r2_hidden @ (sk_B @ X14) @ X14)
% 0.54/0.72          | (v4_ordinal1 @ X14)
% 0.54/0.72          | ~ (v3_ordinal1 @ X14))),
% 0.54/0.72      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.72  thf('67', plain,
% 0.54/0.72      (![X10 : $i, X11 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X10)
% 0.54/0.72          | ~ (r2_hidden @ X11 @ X10)
% 0.54/0.72          | (r1_ordinal1 @ (k1_ordinal1 @ X11) @ X10)
% 0.54/0.72          | ~ (v3_ordinal1 @ X11))),
% 0.54/0.72      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.54/0.72  thf('68', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.54/0.72          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['66', '67'])).
% 0.54/0.72  thf('69', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['68'])).
% 0.54/0.72  thf('70', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['65', '69'])).
% 0.54/0.72  thf('71', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['70'])).
% 0.54/0.72  thf(t34_ordinal1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.72           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.54/0.72             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.54/0.72  thf('72', plain,
% 0.54/0.72      (![X12 : $i, X13 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X12)
% 0.54/0.72          | ~ (r1_ordinal1 @ X13 @ X12)
% 0.54/0.72          | (r2_hidden @ X13 @ (k1_ordinal1 @ X12))
% 0.54/0.72          | ~ (v3_ordinal1 @ X13))),
% 0.54/0.72      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.54/0.72  thf('73', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.54/0.72          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.54/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['71', '72'])).
% 0.54/0.72  thf('74', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.54/0.72          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['73'])).
% 0.54/0.72  thf('75', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.54/0.72          | ~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['64', '74'])).
% 0.54/0.72  thf('76', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['63', '75'])).
% 0.54/0.72  thf('77', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['76'])).
% 0.54/0.72  thf('78', plain,
% 0.54/0.72      (![X6 : $i, X7 : $i]:
% 0.54/0.72         (((X7) = (X6))
% 0.54/0.72          | (r2_hidden @ X7 @ X6)
% 0.54/0.72          | ~ (r2_hidden @ X7 @ (k1_ordinal1 @ X6)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.54/0.72  thf('79', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.54/0.72          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['77', '78'])).
% 0.54/0.72  thf('80', plain,
% 0.54/0.72      (![X14 : $i]:
% 0.54/0.72         (~ (r2_hidden @ (k1_ordinal1 @ (sk_B @ X14)) @ X14)
% 0.54/0.72          | (v4_ordinal1 @ X14)
% 0.54/0.72          | ~ (v3_ordinal1 @ X14))),
% 0.54/0.72      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.54/0.72  thf('81', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0)
% 0.54/0.72          | ~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['79', '80'])).
% 0.54/0.72  thf('82', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X0)
% 0.54/0.72          | (v4_ordinal1 @ X0)
% 0.54/0.72          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['81'])).
% 0.54/0.72  thf('83', plain,
% 0.54/0.72      (![X16 : $i]:
% 0.54/0.72         (~ (v3_ordinal1 @ X16)
% 0.54/0.72          | ((sk_A) != (k1_ordinal1 @ X16))
% 0.54/0.72          | (v3_ordinal1 @ sk_B_1))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('84', plain,
% 0.54/0.72      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16)))
% 0.54/0.72         <= ((![X16 : $i]:
% 0.54/0.72                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.54/0.72      inference('split', [status(esa)], ['83'])).
% 0.54/0.72  thf('85', plain,
% 0.54/0.72      ((![X0 : $i]:
% 0.54/0.72          (((sk_A) != (X0))
% 0.54/0.72           | (v4_ordinal1 @ X0)
% 0.54/0.72           | ~ (v3_ordinal1 @ X0)
% 0.54/0.72           | ~ (v3_ordinal1 @ (sk_B @ X0))))
% 0.54/0.72         <= ((![X16 : $i]:
% 0.54/0.72                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['82', '84'])).
% 0.54/0.72  thf('86', plain,
% 0.54/0.72      (((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.54/0.72         | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.72         | (v4_ordinal1 @ sk_A)))
% 0.54/0.72         <= ((![X16 : $i]:
% 0.54/0.72                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.54/0.72      inference('simplify', [status(thm)], ['85'])).
% 0.54/0.72  thf('87', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('88', plain,
% 0.54/0.72      (((~ (v3_ordinal1 @ (sk_B @ sk_A)) | (v4_ordinal1 @ sk_A)))
% 0.54/0.72         <= ((![X16 : $i]:
% 0.54/0.72                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.54/0.72      inference('simplify_reflect+', [status(thm)], ['86', '87'])).
% 0.54/0.72  thf('89', plain,
% 0.54/0.72      (((~ (v3_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.54/0.72         <= ((![X16 : $i]:
% 0.54/0.72                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['62', '88'])).
% 0.54/0.72  thf('90', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('91', plain,
% 0.54/0.72      ((((v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.54/0.72         <= ((![X16 : $i]:
% 0.54/0.72                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.54/0.72      inference('demod', [status(thm)], ['89', '90'])).
% 0.54/0.72  thf('92', plain,
% 0.54/0.72      (((v4_ordinal1 @ sk_A))
% 0.54/0.72         <= ((![X16 : $i]:
% 0.54/0.72                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.54/0.72      inference('simplify', [status(thm)], ['91'])).
% 0.54/0.72  thf('93', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 0.54/0.72      inference('split', [status(esa)], ['4'])).
% 0.54/0.72  thf('94', plain,
% 0.54/0.72      (~
% 0.54/0.72       (![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))) | 
% 0.54/0.72       ((v4_ordinal1 @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['92', '93'])).
% 0.54/0.72  thf('95', plain, ($false),
% 0.54/0.72      inference('sat_resolution*', [status(thm)],
% 0.54/0.72                ['1', '3', '5', '60', '61', '94'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
