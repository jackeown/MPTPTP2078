%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.coGLplVJw8

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:12 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 819 expanded)
%              Number of leaves         :   19 ( 214 expanded)
%              Depth                    :   23
%              Number of atoms          :  999 (8482 expanded)
%              Number of equality atoms :   92 ( 979 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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
    | ( v3_ordinal1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X16: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( sk_A
       != ( k1_ordinal1 @ X16 ) )
      | ( v4_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_ordinal1 @ X6 ) )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('8',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_ordinal1 @ X6 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(t41_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v4_ordinal1 @ A )
      <=> ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ B @ A )
             => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_ordinal1 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ ( k1_ordinal1 @ X15 ) @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('11',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_1 ) @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('15',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v3_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ( ( r2_hidden @ sk_A @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12','17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( v3_ordinal1 @ X0 )
        | ( r1_ordinal1 @ X0 @ sk_B_1 )
        | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( v3_ordinal1 @ X0 )
        | ( r1_ordinal1 @ X0 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ X11 ) @ X10 )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_ordinal1 @ sk_A @ X0 )
        | ~ ( v3_ordinal1 @ sk_B_1 )
        | ( r2_hidden @ sk_B_1 @ X0 )
        | ~ ( v3_ordinal1 @ X0 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_ordinal1 @ sk_A @ X0 )
        | ( r2_hidden @ sk_B_1 @ X0 )
        | ~ ( v3_ordinal1 @ X0 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r2_hidden @ sk_B_1 @ sk_B_1 ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v3_ordinal1 @ sk_B_1 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_B_1 )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( sk_A
        = ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_ordinal1 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_ordinal1 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ X0 ) ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['40'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( X7
     != ( k1_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ X0 ) ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_ordinal1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( ( sk_C @ sk_B_1 @ sk_A )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('52',plain,
    ( ( ( ( sk_C @ sk_B_1 @ sk_A )
        = sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( sk_A = sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('54',plain,
    ( ( ( ( sk_C @ sk_B_1 @ sk_A )
        = sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('56',plain,(
    ! [X7: $i] :
      ( X7
     != ( k1_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('57',plain,
    ( ( sk_B_1 != sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = sk_B_1 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('60',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( sk_A = sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = sk_B_1 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).

thf('62',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('63',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( sk_B_1 != sk_A )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_B_1 )
   <= ( sk_A
      = ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_A
     != ( k1_ordinal1 @ sk_B_1 ) )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','65'])).

thf('67',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','66'])).

thf('68',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','67'])).

thf('69',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('70',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf(fc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( v1_xboole_0 @ ( k1_ordinal1 @ A ) )
        & ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('72',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ X14 ) )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('73',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_B @ X14 ) @ X14 )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('74',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X11 ) @ X10 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ ( k1_ordinal1 @ X0 ) )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_ordinal1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X0 ) ) @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ ( sk_B @ X14 ) ) @ X14 )
      | ( v4_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t41_ordinal1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v4_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X16: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( sk_A
       != ( k1_ordinal1 @ X16 ) )
      | ( v3_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) )
   <= ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(split,[status(esa)],['90'])).

thf('92',plain,
    ( ! [X16: $i] :
        ( ( sk_A
         != ( k1_ordinal1 @ X16 ) )
        | ~ ( v3_ordinal1 @ X16 ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('93',plain,(
    ! [X16: $i] :
      ( ( sk_A
       != ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','66','92'])).

thf('94',plain,(
    ! [X16: $i] :
      ( ( sk_A
       != ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(simpl_trail,[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( v4_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v4_ordinal1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','67'])).

thf('100',plain,(
    ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','100'])).

thf('102',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_ordinal1 @ sk_A ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['68','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.coGLplVJw8
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 411 iterations in 0.167s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.62  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.36/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.62  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.36/0.62  thf(t42_ordinal1, conjecture,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.36/0.62       ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.36/0.62              ( ![B:$i]:
% 0.36/0.62                ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.36/0.62         ( ~( ( ?[B:$i]:
% 0.36/0.62                ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.36/0.62              ( v4_ordinal1 @ A ) ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i]:
% 0.36/0.62        ( ( v3_ordinal1 @ A ) =>
% 0.36/0.62          ( ( ~( ( ~( v4_ordinal1 @ A ) ) & 
% 0.36/0.62                 ( ![B:$i]:
% 0.36/0.62                   ( ( v3_ordinal1 @ B ) => ( ( A ) != ( k1_ordinal1 @ B ) ) ) ) ) ) & 
% 0.36/0.62            ( ~( ( ?[B:$i]:
% 0.36/0.62                   ( ( ( A ) = ( k1_ordinal1 @ B ) ) & ( v3_ordinal1 @ B ) ) ) & 
% 0.36/0.62                 ( v4_ordinal1 @ A ) ) ) ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t42_ordinal1])).
% 0.36/0.62  thf('0', plain, ((~ (v4_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_1))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('1', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 0.36/0.62      inference('split', [status(esa)], ['0'])).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      ((~ (v4_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      (~ ((v4_ordinal1 @ sk_A)) | (((sk_A) = (k1_ordinal1 @ sk_B_1)))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      (![X16 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X16)
% 0.36/0.62          | ((sk_A) != (k1_ordinal1 @ X16))
% 0.36/0.62          | (v4_ordinal1 @ sk_A))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('5', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 0.36/0.62      inference('split', [status(esa)], ['4'])).
% 0.36/0.62  thf('6', plain,
% 0.36/0.62      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf(t13_ordinal1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.36/0.62       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i]:
% 0.36/0.62         ((r2_hidden @ X5 @ (k1_ordinal1 @ X6)) | ((X5) != (X6)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.36/0.62  thf('8', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_ordinal1 @ X6))),
% 0.36/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.36/0.62  thf('9', plain,
% 0.36/0.62      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['6', '8'])).
% 0.36/0.62  thf(t41_ordinal1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.36/0.62       ( ( v4_ordinal1 @ A ) <=>
% 0.36/0.62         ( ![B:$i]:
% 0.36/0.62           ( ( v3_ordinal1 @ B ) =>
% 0.36/0.62             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 0.36/0.62  thf('10', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         (~ (v4_ordinal1 @ X14)
% 0.36/0.62          | ~ (r2_hidden @ X15 @ X14)
% 0.36/0.62          | (r2_hidden @ (k1_ordinal1 @ X15) @ X14)
% 0.36/0.62          | ~ (v3_ordinal1 @ X15)
% 0.36/0.62          | ~ (v3_ordinal1 @ X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      (((~ (v3_ordinal1 @ sk_A)
% 0.36/0.62         | ~ (v3_ordinal1 @ sk_B_1)
% 0.36/0.62         | (r2_hidden @ (k1_ordinal1 @ sk_B_1) @ sk_A)
% 0.36/0.62         | ~ (v4_ordinal1 @ sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.62  thf('12', plain, ((v3_ordinal1 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['6', '8'])).
% 0.36/0.62  thf(t23_ordinal1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.36/0.62  thf('14', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i]:
% 0.36/0.62         ((v3_ordinal1 @ X8) | ~ (v3_ordinal1 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.36/0.62      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      (((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.62  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (((v3_ordinal1 @ sk_B_1)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('18', plain,
% 0.36/0.62      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf('19', plain,
% 0.36/0.62      ((((r2_hidden @ sk_A @ sk_A) | ~ (v4_ordinal1 @ sk_A)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['11', '12', '17', '18'])).
% 0.36/0.62  thf('20', plain,
% 0.36/0.62      (((r2_hidden @ sk_A @ sk_A))
% 0.36/0.62         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['5', '19'])).
% 0.36/0.62  thf('21', plain,
% 0.36/0.62      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf(t34_ordinal1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.36/0.62           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.36/0.62             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      (![X12 : $i, X13 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X12)
% 0.36/0.62          | ~ (r2_hidden @ X13 @ (k1_ordinal1 @ X12))
% 0.36/0.62          | (r1_ordinal1 @ X13 @ X12)
% 0.36/0.62          | ~ (v3_ordinal1 @ X13))),
% 0.36/0.62      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.36/0.62  thf('23', plain,
% 0.36/0.62      ((![X0 : $i]:
% 0.36/0.62          (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.62           | ~ (v3_ordinal1 @ X0)
% 0.36/0.62           | (r1_ordinal1 @ X0 @ sk_B_1)
% 0.36/0.62           | ~ (v3_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (((v3_ordinal1 @ sk_B_1)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('25', plain,
% 0.36/0.62      ((![X0 : $i]:
% 0.36/0.62          (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.62           | ~ (v3_ordinal1 @ X0)
% 0.36/0.62           | (r1_ordinal1 @ X0 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.62  thf('26', plain,
% 0.36/0.62      ((((r1_ordinal1 @ sk_A @ sk_B_1) | ~ (v3_ordinal1 @ sk_A)))
% 0.36/0.62         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['20', '25'])).
% 0.36/0.62  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('28', plain,
% 0.36/0.62      (((r1_ordinal1 @ sk_A @ sk_B_1))
% 0.36/0.62         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.62  thf('29', plain,
% 0.36/0.62      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf(t33_ordinal1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.36/0.62           ( ( r2_hidden @ A @ B ) <=>
% 0.36/0.62             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.36/0.62  thf('30', plain,
% 0.36/0.62      (![X10 : $i, X11 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X10)
% 0.36/0.62          | ~ (r1_ordinal1 @ (k1_ordinal1 @ X11) @ X10)
% 0.36/0.62          | (r2_hidden @ X11 @ X10)
% 0.36/0.62          | ~ (v3_ordinal1 @ X11))),
% 0.36/0.62      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.36/0.62  thf('31', plain,
% 0.36/0.62      ((![X0 : $i]:
% 0.36/0.62          (~ (r1_ordinal1 @ sk_A @ X0)
% 0.36/0.62           | ~ (v3_ordinal1 @ sk_B_1)
% 0.36/0.62           | (r2_hidden @ sk_B_1 @ X0)
% 0.36/0.62           | ~ (v3_ordinal1 @ X0)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.62  thf('32', plain,
% 0.36/0.62      (((v3_ordinal1 @ sk_B_1)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('33', plain,
% 0.36/0.62      ((![X0 : $i]:
% 0.36/0.62          (~ (r1_ordinal1 @ sk_A @ X0)
% 0.36/0.62           | (r2_hidden @ sk_B_1 @ X0)
% 0.36/0.62           | ~ (v3_ordinal1 @ X0)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.62  thf('34', plain,
% 0.36/0.62      (((~ (v3_ordinal1 @ sk_B_1) | (r2_hidden @ sk_B_1 @ sk_B_1)))
% 0.36/0.62         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['28', '33'])).
% 0.36/0.62  thf('35', plain,
% 0.36/0.62      (((v3_ordinal1 @ sk_B_1)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('36', plain,
% 0.36/0.62      (((r2_hidden @ sk_B_1 @ sk_B_1))
% 0.36/0.62         <= (((v4_ordinal1 @ sk_A)) & (((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.62  thf('37', plain,
% 0.36/0.62      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf(t2_tarski, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.36/0.62       ( ( A ) = ( B ) ) ))).
% 0.36/0.62  thf('38', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (((X1) = (X0))
% 0.36/0.62          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.36/0.62          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t2_tarski])).
% 0.36/0.62  thf('39', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i]:
% 0.36/0.62         ((r2_hidden @ X5 @ (k1_ordinal1 @ X6)) | ~ (r2_hidden @ X5 @ X6))),
% 0.36/0.62      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.36/0.62  thf('40', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.36/0.62          | ((X1) = (X0))
% 0.36/0.62          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_ordinal1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.62  thf('41', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (((k1_ordinal1 @ X0) = (X0))
% 0.36/0.62          | (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ X0)) @ (k1_ordinal1 @ X0)))),
% 0.36/0.62      inference('eq_fact', [status(thm)], ['40'])).
% 0.36/0.62  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.36/0.62  thf('42', plain, (![X7 : $i]: ((X7) != (k1_ordinal1 @ X7))),
% 0.36/0.62      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.36/0.62  thf('43', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ X0)) @ (k1_ordinal1 @ X0))),
% 0.36/0.62      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.36/0.62  thf('44', plain,
% 0.36/0.62      (((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['37', '43'])).
% 0.36/0.62  thf('45', plain,
% 0.36/0.62      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf('46', plain,
% 0.36/0.62      (((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.62  thf('47', plain,
% 0.36/0.62      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf('48', plain,
% 0.36/0.62      (![X4 : $i, X5 : $i]:
% 0.36/0.62         (((X5) = (X4))
% 0.36/0.62          | (r2_hidden @ X5 @ X4)
% 0.36/0.62          | ~ (r2_hidden @ X5 @ (k1_ordinal1 @ X4)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.36/0.62  thf('49', plain,
% 0.36/0.62      ((![X0 : $i]:
% 0.36/0.62          (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.62           | (r2_hidden @ X0 @ sk_B_1)
% 0.36/0.62           | ((X0) = (sk_B_1))))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.62  thf('50', plain,
% 0.36/0.62      (((((sk_C @ sk_B_1 @ sk_A) = (sk_B_1))
% 0.36/0.62         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['46', '49'])).
% 0.36/0.62  thf('51', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (((X1) = (X0))
% 0.36/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.36/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t2_tarski])).
% 0.36/0.62  thf('52', plain,
% 0.36/0.62      (((((sk_C @ sk_B_1 @ sk_A) = (sk_B_1))
% 0.36/0.62         | ~ (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.62         | ((sk_A) = (sk_B_1)))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.62  thf('53', plain,
% 0.36/0.62      (((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.62  thf('54', plain,
% 0.36/0.62      (((((sk_C @ sk_B_1 @ sk_A) = (sk_B_1)) | ((sk_A) = (sk_B_1))))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.62  thf('55', plain,
% 0.36/0.62      ((((sk_A) = (k1_ordinal1 @ sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('split', [status(esa)], ['2'])).
% 0.36/0.62  thf('56', plain, (![X7 : $i]: ((X7) != (k1_ordinal1 @ X7))),
% 0.36/0.62      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.36/0.62  thf('57', plain,
% 0.36/0.62      ((((sk_B_1) != (sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.36/0.62  thf('58', plain,
% 0.36/0.62      ((((sk_C @ sk_B_1 @ sk_A) = (sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('simplify_reflect-', [status(thm)], ['54', '57'])).
% 0.36/0.62  thf('59', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (((X1) = (X0))
% 0.36/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.36/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t2_tarski])).
% 0.36/0.62  thf('60', plain,
% 0.36/0.62      (((~ (r2_hidden @ sk_B_1 @ sk_B_1)
% 0.36/0.62         | ~ (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.62         | ((sk_A) = (sk_B_1)))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.62  thf('61', plain,
% 0.36/0.62      ((((sk_C @ sk_B_1 @ sk_A) = (sk_B_1)))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('simplify_reflect-', [status(thm)], ['54', '57'])).
% 0.36/0.62  thf('62', plain,
% 0.36/0.62      (((r2_hidden @ sk_B_1 @ sk_A)) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['6', '8'])).
% 0.36/0.62  thf('63', plain,
% 0.36/0.62      (((~ (r2_hidden @ sk_B_1 @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.36/0.62  thf('64', plain,
% 0.36/0.62      ((((sk_B_1) != (sk_A))) <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.36/0.62  thf('65', plain,
% 0.36/0.62      ((~ (r2_hidden @ sk_B_1 @ sk_B_1))
% 0.36/0.62         <= ((((sk_A) = (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.62      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.36/0.62  thf('66', plain,
% 0.36/0.62      (~ (((sk_A) = (k1_ordinal1 @ sk_B_1))) | ~ ((v4_ordinal1 @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['36', '65'])).
% 0.36/0.62  thf('67', plain, (~ ((v4_ordinal1 @ sk_A))),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['3', '66'])).
% 0.36/0.62  thf('68', plain, (~ (v4_ordinal1 @ sk_A)),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['1', '67'])).
% 0.36/0.62  thf('69', plain,
% 0.36/0.62      (![X14 : $i]:
% 0.36/0.62         ((v3_ordinal1 @ (sk_B @ X14))
% 0.36/0.62          | (v4_ordinal1 @ X14)
% 0.36/0.62          | ~ (v3_ordinal1 @ X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.36/0.62  thf('70', plain,
% 0.36/0.62      (![X14 : $i]:
% 0.36/0.62         ((v3_ordinal1 @ (sk_B @ X14))
% 0.36/0.62          | (v4_ordinal1 @ X14)
% 0.36/0.62          | ~ (v3_ordinal1 @ X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.36/0.62  thf(fc2_ordinal1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.36/0.62       ( ( ~( v1_xboole_0 @ ( k1_ordinal1 @ A ) ) ) & 
% 0.36/0.62         ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ))).
% 0.36/0.62  thf('71', plain,
% 0.36/0.62      (![X3 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X3)) | ~ (v3_ordinal1 @ X3))),
% 0.36/0.62      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.36/0.62  thf('72', plain,
% 0.36/0.62      (![X14 : $i]:
% 0.36/0.62         ((v3_ordinal1 @ (sk_B @ X14))
% 0.36/0.62          | (v4_ordinal1 @ X14)
% 0.36/0.62          | ~ (v3_ordinal1 @ X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.36/0.62  thf('73', plain,
% 0.36/0.62      (![X14 : $i]:
% 0.36/0.62         ((r2_hidden @ (sk_B @ X14) @ X14)
% 0.36/0.62          | (v4_ordinal1 @ X14)
% 0.36/0.62          | ~ (v3_ordinal1 @ X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.36/0.62  thf('74', plain,
% 0.36/0.62      (![X10 : $i, X11 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X10)
% 0.36/0.62          | ~ (r2_hidden @ X11 @ X10)
% 0.36/0.62          | (r1_ordinal1 @ (k1_ordinal1 @ X11) @ X10)
% 0.36/0.62          | ~ (v3_ordinal1 @ X11))),
% 0.36/0.62      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.36/0.62  thf('75', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.36/0.62          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.62  thf('76', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ (sk_B @ X0))
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.62      inference('simplify', [status(thm)], ['75'])).
% 0.36/0.62  thf('77', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | (r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['72', '76'])).
% 0.36/0.62  thf('78', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((r1_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.62      inference('simplify', [status(thm)], ['77'])).
% 0.36/0.62  thf('79', plain,
% 0.36/0.62      (![X12 : $i, X13 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X12)
% 0.36/0.62          | ~ (r1_ordinal1 @ X13 @ X12)
% 0.36/0.62          | (r2_hidden @ X13 @ (k1_ordinal1 @ X12))
% 0.36/0.62          | ~ (v3_ordinal1 @ X13))),
% 0.36/0.62      inference('cnf', [status(esa)], [t34_ordinal1])).
% 0.36/0.62  thf('80', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.36/0.62          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.36/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['78', '79'])).
% 0.36/0.62  thf('81', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.36/0.62          | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B @ X0)))
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.62      inference('simplify', [status(thm)], ['80'])).
% 0.36/0.62  thf('82', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ (sk_B @ X0))
% 0.36/0.62          | ~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['71', '81'])).
% 0.36/0.62  thf('83', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['70', '82'])).
% 0.36/0.62  thf('84', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ (k1_ordinal1 @ X0))
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.62      inference('simplify', [status(thm)], ['83'])).
% 0.36/0.62  thf('85', plain,
% 0.36/0.62      (![X4 : $i, X5 : $i]:
% 0.36/0.62         (((X5) = (X4))
% 0.36/0.62          | (r2_hidden @ X5 @ X4)
% 0.36/0.62          | ~ (r2_hidden @ X5 @ (k1_ordinal1 @ X4)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.36/0.62  thf('86', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | (r2_hidden @ (k1_ordinal1 @ (sk_B @ X0)) @ X0)
% 0.36/0.62          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.36/0.62  thf('87', plain,
% 0.36/0.62      (![X14 : $i]:
% 0.36/0.62         (~ (r2_hidden @ (k1_ordinal1 @ (sk_B @ X14)) @ X14)
% 0.36/0.62          | (v4_ordinal1 @ X14)
% 0.36/0.62          | ~ (v3_ordinal1 @ X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_ordinal1])).
% 0.36/0.62  thf('88', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (((k1_ordinal1 @ (sk_B @ X0)) = (X0))
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['86', '87'])).
% 0.36/0.62  thf('89', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X0)
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ((k1_ordinal1 @ (sk_B @ X0)) = (X0)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['88'])).
% 0.36/0.62  thf('90', plain,
% 0.36/0.62      (![X16 : $i]:
% 0.36/0.62         (~ (v3_ordinal1 @ X16)
% 0.36/0.62          | ((sk_A) != (k1_ordinal1 @ X16))
% 0.36/0.62          | (v3_ordinal1 @ sk_B_1))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('91', plain,
% 0.36/0.62      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16)))
% 0.36/0.62         <= ((![X16 : $i]:
% 0.36/0.62                (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))))),
% 0.36/0.62      inference('split', [status(esa)], ['90'])).
% 0.36/0.62  thf('92', plain,
% 0.36/0.62      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))) | 
% 0.36/0.62       ((v4_ordinal1 @ sk_A))),
% 0.36/0.62      inference('split', [status(esa)], ['4'])).
% 0.36/0.62  thf('93', plain,
% 0.36/0.62      ((![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16)))),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['3', '66', '92'])).
% 0.36/0.62  thf('94', plain,
% 0.36/0.62      (![X16 : $i]: (((sk_A) != (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['91', '93'])).
% 0.36/0.62  thf('95', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (((sk_A) != (X0))
% 0.36/0.62          | (v4_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ X0)
% 0.36/0.62          | ~ (v3_ordinal1 @ (sk_B @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['89', '94'])).
% 0.36/0.62  thf('96', plain,
% 0.36/0.62      ((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.36/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.36/0.62        | (v4_ordinal1 @ sk_A))),
% 0.36/0.62      inference('simplify', [status(thm)], ['95'])).
% 0.36/0.62  thf('97', plain, ((v3_ordinal1 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('98', plain, ((~ (v3_ordinal1 @ (sk_B @ sk_A)) | (v4_ordinal1 @ sk_A))),
% 0.36/0.62      inference('simplify_reflect+', [status(thm)], ['96', '97'])).
% 0.36/0.62  thf('99', plain, (~ (v4_ordinal1 @ sk_A)),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['1', '67'])).
% 0.36/0.62  thf('100', plain, (~ (v3_ordinal1 @ (sk_B @ sk_A))),
% 0.36/0.62      inference('clc', [status(thm)], ['98', '99'])).
% 0.36/0.62  thf('101', plain, ((~ (v3_ordinal1 @ sk_A) | (v4_ordinal1 @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['69', '100'])).
% 0.36/0.62  thf('102', plain, ((v3_ordinal1 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('103', plain, ((v4_ordinal1 @ sk_A)),
% 0.36/0.62      inference('demod', [status(thm)], ['101', '102'])).
% 0.36/0.62  thf('104', plain, ($false), inference('demod', [status(thm)], ['68', '103'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
