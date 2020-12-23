%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5wQEzWCXm6

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:11 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 150 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   20
%              Number of atoms          :  714 (1597 expanded)
%              Number of equality atoms :   59 ( 145 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

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
    ! [X17: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( sk_A
       != ( k1_ordinal1 @ X17 ) )
      | ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) )
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
    ! [X17: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( sk_A
       != ( k1_ordinal1 @ X17 ) )
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
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_ordinal1 @ X7 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_ordinal1 @ X13 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k1_ordinal1 @ X14 ) @ X13 )
      | ~ ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
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
    ( ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('24',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X13 ) )
      | ( v4_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('25',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X13 ) )
      | ( v4_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf(fc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( v1_xboole_0 @ ( k1_ordinal1 @ A ) )
        & ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X6 ) )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ( X12 = X11 )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('28',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X13 ) ) @ X13 )
      | ( v4_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( k1_ordinal1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ ( sk_B @ X0 ) )
      | ( X0
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ ( sk_B @ X13 ) @ X13 )
      | ( v4_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_B @ X0 ) )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( X0
        = ( sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X17: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( sk_A
       != ( k1_ordinal1 @ X17 ) )
      | ( v3_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( sk_A != X0 )
        | ( X0
          = ( sk_B @ X0 ) )
        | ( v4_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ X0 )
        | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A )
      | ( sk_A
        = ( sk_B @ sk_A ) ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A )
      | ( sk_A
        = ( sk_B @ sk_A ) ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference('simplify_reflect+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A )
      | ( sk_A
        = ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference('sup-',[status(thm)],['24','46'])).

thf('48',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v4_ordinal1 @ sk_A )
      | ( sk_A
        = ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( sk_A
        = ( sk_B @ sk_A ) )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ ( sk_B @ X13 ) @ X13 )
      | ( v4_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ~ ( r1_tarski @ sk_A @ sk_A )
      | ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v4_ordinal1 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(demod,[status(thm)],['54','58','59'])).

thf('61',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ! [X17: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X17 ) )
        | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('63',plain,
    ( ~ ! [X17: $i] :
          ( ( sk_A
           != ( k1_ordinal1 @ X17 ) )
          | ~ ( v3_ordinal1 @ X17 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','22','23','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5wQEzWCXm6
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.97/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.97/1.14  % Solved by: fo/fo7.sh
% 0.97/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.14  % done 1048 iterations in 0.686s
% 0.97/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.97/1.14  % SZS output start Refutation
% 0.97/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.97/1.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.97/1.14  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.97/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.14  thf(sk_B_type, type, sk_B: $i > $i).
% 0.97/1.14  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.97/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.14  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.97/1.14  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.97/1.14  thf(t42_ordinal1, conjecture,
% 0.97/1.14    (![A:$i]:
% 0.97/1.14     ( ( v3_ordinal1 @ A ) =>
% 0.97/1.14       ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.97/1.14              ( ![B:$i]:
% 0.97/1.14                ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.97/1.14         ( ~( ( ?[B:$i]:
% 0.97/1.14                ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.97/1.14              ( v4_ordinal1 @ A ) ) ) ) ))).
% 0.97/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.14    (~( ![A:$i]:
% 0.97/1.14        ( ( v3_ordinal1 @ A ) =>
% 0.97/1.14          ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.97/1.14                 ( ![B:$i]:
% 0.97/1.14                   ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.97/1.14            ( ~( ( ?[B:$i]:
% 0.97/1.14                   ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.97/1.14                 ( v4_ordinal1 @ A ) ) ) ) ) )),
% 0.97/1.14    inference('cnf.neg', [status(esa)], [t42_ordinal1])).
% 0.97/1.14  thf('0', plain,
% 0.97/1.14      ((~ (v4_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('1', plain,
% 0.97/1.14      (~ ((v4_ordinal1 @ sk_A)) | (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.97/1.14      inference('split', [status(esa)], ['0'])).
% 0.97/1.14  thf('2', plain,
% 0.97/1.14      (![X17 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X17)
% 0.97/1.14          | ((sk_A) != (k1_ordinal1 @ X17))
% 0.97/1.14          | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('3', plain,
% 0.97/1.14      ((![X17 : $i]: (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))) | 
% 0.97/1.14       (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.97/1.14      inference('split', [status(esa)], ['2'])).
% 0.97/1.14  thf('4', plain, ((~ (v4_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_1))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('5', plain, (~ ((v4_ordinal1 @ sk_A)) | ((v3_ordinal1 @ sk_B_1))),
% 0.97/1.14      inference('split', [status(esa)], ['4'])).
% 0.97/1.14  thf('6', plain,
% 0.97/1.14      (![X17 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X17)
% 0.97/1.14          | ((sk_A) != (k1_ordinal1 @ X17))
% 0.97/1.14          | (v4_ordinal1 @ sk_A))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('7', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 0.97/1.14      inference('split', [status(esa)], ['6'])).
% 0.97/1.14  thf('8', plain, (((v3_ordinal1 @ sk_B_1)) <= (((v3_ordinal1 @ sk_B_1)))),
% 0.97/1.14      inference('split', [status(esa)], ['4'])).
% 0.97/1.14  thf('9', plain,
% 0.97/1.14      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.97/1.14         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('split', [status(esa)], ['0'])).
% 0.97/1.14  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.97/1.14  thf('10', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_ordinal1 @ X7))),
% 0.97/1.14      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.97/1.14  thf('11', plain,
% 0.97/1.14      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('sup+', [status(thm)], ['9', '10'])).
% 0.97/1.14  thf(t41_ordinal1, axiom,
% 0.97/1.14    (![A:$i]:
% 0.97/1.14     ( ( v3_ordinal1 @ A ) =>
% 0.97/1.14       ( ( v4_ordinal1 @ A ) <=>
% 0.97/1.14         ( ![B:$i]:
% 0.97/1.14           ( ( v3_ordinal1 @ B ) =>
% 0.97/1.14             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 0.97/1.14  thf('12', plain,
% 0.97/1.14      (![X13 : $i, X14 : $i]:
% 0.97/1.14         (~ (v4_ordinal1 @ X13)
% 0.97/1.14          | ~ (r2_hidden @ X14 @ X13)
% 0.97/1.14          | (r2_hidden @ (k1_ordinal1 @ X14) @ X13)
% 0.97/1.14          | ~ (v3_ordinal1 @ X14)
% 0.97/1.14          | ~ (v3_ordinal1 @ X13))),
% 0.97/1.14      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.97/1.14  thf('13', plain,
% 0.97/1.14      (((~ (v3_ordinal1 @ sk_A)
% 0.97/1.14         | ~ (v3_ordinal1 @ sk_B_1)
% 0.97/1.14         | (r2_hidden @ (k1_ordinal1 @ sk_B_1) @ sk_A)
% 0.97/1.14         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['11', '12'])).
% 0.97/1.14  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('15', plain,
% 0.97/1.14      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.97/1.14         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('split', [status(esa)], ['0'])).
% 0.97/1.14  thf('16', plain,
% 0.97/1.14      (((~ (v3_ordinal1 @ sk_B_1)
% 0.97/1.14         | (r2_hidden @ sk_A @ sk_A)
% 0.97/1.14         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.97/1.14  thf('17', plain,
% 0.97/1.14      (((~ (v4_ordinal1 @ sk_A) | (r2_hidden @ sk_A @ sk_A)))
% 0.97/1.14         <= (((v3_ordinal1 @ sk_B_1)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['8', '16'])).
% 0.97/1.14  thf('18', plain,
% 0.97/1.14      (((r2_hidden @ sk_A @ sk_A))
% 0.97/1.14         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.97/1.14             ((v4_ordinal1 @ sk_A)) & 
% 0.97/1.14             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['7', '17'])).
% 0.97/1.14  thf(antisymmetry_r2_hidden, axiom,
% 0.97/1.14    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.97/1.14  thf('19', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.97/1.14      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.97/1.14  thf('20', plain,
% 0.97/1.14      ((~ (r2_hidden @ sk_A @ sk_A))
% 0.97/1.14         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.97/1.14             ((v4_ordinal1 @ sk_A)) & 
% 0.97/1.14             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['18', '19'])).
% 0.97/1.14  thf('21', plain,
% 0.97/1.14      (((r2_hidden @ sk_A @ sk_A))
% 0.97/1.14         <= (((v3_ordinal1 @ sk_B_1)) & 
% 0.97/1.14             ((v4_ordinal1 @ sk_A)) & 
% 0.97/1.14             (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['7', '17'])).
% 0.97/1.14  thf('22', plain,
% 0.97/1.14      (~ ((v4_ordinal1 @ sk_A)) | ~ (((sk_A) = (k1_ordinal1 @ sk_B_1))) | 
% 0.97/1.14       ~ ((v3_ordinal1 @ sk_B_1))),
% 0.97/1.14      inference('demod', [status(thm)], ['20', '21'])).
% 0.97/1.14  thf('23', plain,
% 0.97/1.14      ((![X17 : $i]: (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))) | 
% 0.97/1.14       ((v4_ordinal1 @ sk_A))),
% 0.97/1.14      inference('split', [status(esa)], ['6'])).
% 0.97/1.14  thf('24', plain,
% 0.97/1.14      (![X13 : $i]:
% 0.97/1.14         ((v3_ordinal1 @ (sk_B @ X13))
% 0.97/1.14          | (v4_ordinal1 @ X13)
% 0.97/1.14          | ~ (v3_ordinal1 @ X13))),
% 0.97/1.14      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.97/1.14  thf('25', plain,
% 0.97/1.14      (![X13 : $i]:
% 0.97/1.14         ((v3_ordinal1 @ (sk_B @ X13))
% 0.97/1.14          | (v4_ordinal1 @ X13)
% 0.97/1.14          | ~ (v3_ordinal1 @ X13))),
% 0.97/1.14      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.97/1.14  thf(fc2_ordinal1, axiom,
% 0.97/1.14    (![A:$i]:
% 0.97/1.14     ( ( v3_ordinal1 @ A ) =>
% 0.97/1.14       ( ( ~( v1_xboole_0 @ ( k1_ordinal1 @ A ) ) ) & 
% 0.97/1.14         ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ))).
% 0.97/1.14  thf('26', plain,
% 0.97/1.14      (![X6 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X6)) | ~ (v3_ordinal1 @ X6))),
% 0.97/1.14      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.97/1.14  thf(t24_ordinal1, axiom,
% 0.97/1.14    (![A:$i]:
% 0.97/1.14     ( ( v3_ordinal1 @ A ) =>
% 0.97/1.14       ( ![B:$i]:
% 0.97/1.14         ( ( v3_ordinal1 @ B ) =>
% 0.97/1.14           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.97/1.14                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.97/1.14  thf('27', plain,
% 0.97/1.14      (![X11 : $i, X12 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X11)
% 0.97/1.14          | (r2_hidden @ X12 @ X11)
% 0.97/1.14          | ((X12) = (X11))
% 0.97/1.14          | (r2_hidden @ X11 @ X12)
% 0.97/1.14          | ~ (v3_ordinal1 @ X12))),
% 0.97/1.14      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.97/1.14  thf('28', plain,
% 0.97/1.14      (![X13 : $i]:
% 0.97/1.14         (~ (r2_hidden @ (k1_ordinal1 @ (sk_B @ X13)) @ X13)
% 0.97/1.14          | (v4_ordinal1 @ X13)
% 0.97/1.14          | ~ (v3_ordinal1 @ X13))),
% 0.97/1.14      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.97/1.14  thf('29', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.97/1.14          | (r2_hidden @ X0 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.97/1.14          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.97/1.14          | ~ (v3_ordinal1 @ X0)
% 0.97/1.14          | ~ (v3_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0))),
% 0.97/1.14      inference('sup-', [status(thm)], ['27', '28'])).
% 0.97/1.14  thf('30', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         ((v4_ordinal1 @ X0)
% 0.97/1.14          | ~ (v3_ordinal1 @ X0)
% 0.97/1.14          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.97/1.14          | (r2_hidden @ X0 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.97/1.14          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0))))),
% 0.97/1.14      inference('simplify', [status(thm)], ['29'])).
% 0.97/1.14  thf('31', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.97/1.14          | (r2_hidden @ X0 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.97/1.14          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.97/1.14          | ~ (v3_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0))),
% 0.97/1.14      inference('sup-', [status(thm)], ['26', '30'])).
% 0.97/1.14  thf('32', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | ~ (v3_ordinal1 @ X0)
% 0.97/1.14          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.97/1.14          | (r2_hidden @ X0 @ (k1_ordinal1 @ (sk_B @ X0))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['25', '31'])).
% 0.97/1.14  thf('33', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         ((r2_hidden @ X0 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.97/1.14          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.97/1.14      inference('simplify', [status(thm)], ['32'])).
% 0.97/1.14  thf(t13_ordinal1, axiom,
% 0.97/1.14    (![A:$i,B:$i]:
% 0.97/1.14     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.97/1.14       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.97/1.14  thf('34', plain,
% 0.97/1.14      (![X8 : $i, X9 : $i]:
% 0.97/1.14         (((X9) = (X8))
% 0.97/1.14          | (r2_hidden @ X9 @ X8)
% 0.97/1.14          | ~ (r2_hidden @ X9 @ (k1_ordinal1 @ X8)))),
% 0.97/1.14      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.97/1.14  thf('35', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.97/1.14          | (r2_hidden @ X0 @ (sk_B @ X0))
% 0.97/1.14          | ((X0) = (sk_B @ X0)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['33', '34'])).
% 0.97/1.14  thf('36', plain,
% 0.97/1.14      (![X13 : $i]:
% 0.97/1.14         ((r2_hidden @ (sk_B @ X13) @ X13)
% 0.97/1.14          | (v4_ordinal1 @ X13)
% 0.97/1.14          | ~ (v3_ordinal1 @ X13))),
% 0.97/1.14      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.97/1.14  thf('37', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.97/1.14      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.97/1.14  thf('38', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | ~ (r2_hidden @ X0 @ (sk_B @ X0)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['36', '37'])).
% 0.97/1.14  thf('39', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (((X0) = (sk_B @ X0))
% 0.97/1.14          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | ~ (v3_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.97/1.14      inference('sup-', [status(thm)], ['35', '38'])).
% 0.97/1.14  thf('40', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.97/1.14          | ((X0) = (sk_B @ X0)))),
% 0.97/1.14      inference('simplify', [status(thm)], ['39'])).
% 0.97/1.14  thf('41', plain,
% 0.97/1.14      (![X17 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X17)
% 0.97/1.14          | ((sk_A) != (k1_ordinal1 @ X17))
% 0.97/1.14          | (v3_ordinal1 @ sk_B_1))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('42', plain,
% 0.97/1.14      ((![X17 : $i]: (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17)))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('split', [status(esa)], ['41'])).
% 0.97/1.14  thf('43', plain,
% 0.97/1.14      ((![X0 : $i]:
% 0.97/1.14          (((sk_A) != (X0))
% 0.97/1.14           | ((X0) = (sk_B @ X0))
% 0.97/1.14           | (v4_ordinal1 @ X0)
% 0.97/1.14           | ~ (v3_ordinal1 @ X0)
% 0.97/1.14           | ~ (v3_ordinal1 @ (sk_B @ X0))))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['40', '42'])).
% 0.97/1.14  thf('44', plain,
% 0.97/1.14      (((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.97/1.14         | ~ (v3_ordinal1 @ sk_A)
% 0.97/1.14         | (v4_ordinal1 @ sk_A)
% 0.97/1.14         | ((sk_A) = (sk_B @ sk_A))))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('simplify', [status(thm)], ['43'])).
% 0.97/1.14  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('46', plain,
% 0.97/1.14      (((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.97/1.14         | (v4_ordinal1 @ sk_A)
% 0.97/1.14         | ((sk_A) = (sk_B @ sk_A))))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('simplify_reflect+', [status(thm)], ['44', '45'])).
% 0.97/1.14  thf('47', plain,
% 0.97/1.14      (((~ (v3_ordinal1 @ sk_A)
% 0.97/1.14         | (v4_ordinal1 @ sk_A)
% 0.97/1.14         | ((sk_A) = (sk_B @ sk_A))
% 0.97/1.14         | (v4_ordinal1 @ sk_A)))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['24', '46'])).
% 0.97/1.14  thf('48', plain, ((v3_ordinal1 @ sk_A)),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('49', plain,
% 0.97/1.14      ((((v4_ordinal1 @ sk_A) | ((sk_A) = (sk_B @ sk_A)) | (v4_ordinal1 @ sk_A)))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('demod', [status(thm)], ['47', '48'])).
% 0.97/1.14  thf('50', plain,
% 0.97/1.14      (((((sk_A) = (sk_B @ sk_A)) | (v4_ordinal1 @ sk_A)))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('simplify', [status(thm)], ['49'])).
% 0.97/1.14  thf('51', plain,
% 0.97/1.14      (![X13 : $i]:
% 0.97/1.14         ((r2_hidden @ (sk_B @ X13) @ X13)
% 0.97/1.14          | (v4_ordinal1 @ X13)
% 0.97/1.14          | ~ (v3_ordinal1 @ X13))),
% 0.97/1.14      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.97/1.14  thf(t7_ordinal1, axiom,
% 0.97/1.14    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.97/1.14  thf('52', plain,
% 0.97/1.14      (![X15 : $i, X16 : $i]:
% 0.97/1.14         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.97/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.97/1.14  thf('53', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (v3_ordinal1 @ X0)
% 0.97/1.14          | (v4_ordinal1 @ X0)
% 0.97/1.14          | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['51', '52'])).
% 0.97/1.14  thf('54', plain,
% 0.97/1.14      (((~ (r1_tarski @ sk_A @ sk_A)
% 0.97/1.14         | (v4_ordinal1 @ sk_A)
% 0.97/1.14         | (v4_ordinal1 @ sk_A)
% 0.97/1.14         | ~ (v3_ordinal1 @ sk_A)))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('sup-', [status(thm)], ['50', '53'])).
% 0.97/1.14  thf(d3_tarski, axiom,
% 0.97/1.14    (![A:$i,B:$i]:
% 0.97/1.14     ( ( r1_tarski @ A @ B ) <=>
% 0.97/1.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.97/1.14  thf('55', plain,
% 0.97/1.14      (![X3 : $i, X5 : $i]:
% 0.97/1.14         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.97/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.14  thf('56', plain,
% 0.97/1.14      (![X3 : $i, X5 : $i]:
% 0.97/1.14         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.97/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.14  thf('57', plain,
% 0.97/1.14      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.97/1.14      inference('sup-', [status(thm)], ['55', '56'])).
% 0.97/1.14  thf('58', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.97/1.14      inference('simplify', [status(thm)], ['57'])).
% 0.97/1.14  thf('59', plain, ((v3_ordinal1 @ sk_A)),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('60', plain,
% 0.97/1.14      ((((v4_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A)))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('demod', [status(thm)], ['54', '58', '59'])).
% 0.97/1.14  thf('61', plain,
% 0.97/1.14      (((v4_ordinal1 @ sk_A))
% 0.97/1.14         <= ((![X17 : $i]:
% 0.97/1.14                (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))))),
% 0.97/1.14      inference('simplify', [status(thm)], ['60'])).
% 0.97/1.14  thf('62', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 0.97/1.14      inference('split', [status(esa)], ['4'])).
% 0.97/1.14  thf('63', plain,
% 0.97/1.14      (~
% 0.97/1.14       (![X17 : $i]: (((sk_A) != (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))) | 
% 0.97/1.14       ((v4_ordinal1 @ sk_A))),
% 0.97/1.14      inference('sup-', [status(thm)], ['61', '62'])).
% 0.97/1.14  thf('64', plain, ($false),
% 0.97/1.14      inference('sat_resolution*', [status(thm)],
% 0.97/1.14                ['1', '3', '5', '22', '23', '63'])).
% 0.97/1.14  
% 0.97/1.14  % SZS output end Refutation
% 0.97/1.14  
% 0.97/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
