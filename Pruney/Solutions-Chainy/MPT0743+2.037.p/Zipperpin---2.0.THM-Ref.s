%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T2ejnbwuVh

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:57 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 525 expanded)
%              Number of leaves         :   17 ( 152 expanded)
%              Depth                    :   24
%              Number of atoms          :  821 (4357 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('0',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('7',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_ordinal1 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('36',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ( ~ ( r1_tarski @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('45',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','48','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','50'])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X3 @ X4 )
      | ( r1_ordinal1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('60',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ( X13 = X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( ( k1_ordinal1 @ sk_A )
        = sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','48'])).

thf('71',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['52','71'])).

thf('73',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k1_ordinal1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('76',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('78',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('80',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','50'])).

thf('84',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['78','87'])).

thf('89',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('90',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','48'])).

thf('91',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r1_ordinal1 @ sk_B @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X3 @ X4 )
      | ( r1_ordinal1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_B ) ),
    inference(eq_fact,[status(thm)],['95'])).

thf('97',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r1_ordinal1 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['92','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['51','99','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T2ejnbwuVh
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 214 iterations in 0.129s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.37/0.59  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.37/0.59  thf(t33_ordinal1, conjecture,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.59           ( ( r2_hidden @ A @ B ) <=>
% 0.37/0.59             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i]:
% 0.37/0.59        ( ( v3_ordinal1 @ A ) =>
% 0.37/0.59          ( ![B:$i]:
% 0.37/0.59            ( ( v3_ordinal1 @ B ) =>
% 0.37/0.59              ( ( r2_hidden @ A @ B ) <=>
% 0.37/0.59                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain,
% 0.37/0.59      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf(t7_ordinal1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X17 : $i, X18 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.37/0.59        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.37/0.59       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('split', [status(esa)], ['4'])).
% 0.37/0.59  thf(t29_ordinal1, axiom,
% 0.37/0.59    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X16 : $i]:
% 0.37/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))),
% 0.37/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf(redefinition_r1_ordinal1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.59       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X6)
% 0.37/0.59          | ~ (v3_ordinal1 @ X7)
% 0.37/0.59          | (r1_tarski @ X6 @ X7)
% 0.37/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.59  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['6', '11'])).
% 0.37/0.59  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.59  thf(t26_ordinal1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.59           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X14 : $i, X15 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X14)
% 0.37/0.59          | (r1_ordinal1 @ X15 @ X14)
% 0.37/0.59          | (r2_hidden @ X14 @ X15)
% 0.37/0.59          | ~ (v3_ordinal1 @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.59  thf(t13_ordinal1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.59       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (![X10 : $i, X11 : $i]:
% 0.37/0.59         ((r2_hidden @ X10 @ (k1_ordinal1 @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.37/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (![X17 : $i, X18 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X1)
% 0.37/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      (((~ (v3_ordinal1 @ sk_A)
% 0.37/0.59         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_B)))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['14', '19'])).
% 0.37/0.59  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (((r1_ordinal1 @ sk_A @ sk_B))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X6)
% 0.37/0.59          | ~ (v3_ordinal1 @ X7)
% 0.37/0.59          | (r1_tarski @ X6 @ X7)
% 0.37/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      ((((r1_tarski @ sk_A @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_A)))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf('26', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (((r1_tarski @ sk_A @ sk_B))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      (![X14 : $i, X15 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X14)
% 0.37/0.59          | (r1_ordinal1 @ X15 @ X14)
% 0.37/0.59          | (r2_hidden @ X14 @ X15)
% 0.37/0.59          | ~ (v3_ordinal1 @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['4'])).
% 0.37/0.59  thf('31', plain,
% 0.37/0.59      (((~ (v3_ordinal1 @ sk_B)
% 0.37/0.59         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.59  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('34', plain,
% 0.37/0.59      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.37/0.59  thf('35', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X6)
% 0.37/0.59          | ~ (v3_ordinal1 @ X7)
% 0.37/0.59          | (r1_tarski @ X6 @ X7)
% 0.37/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.59  thf('36', plain,
% 0.37/0.59      ((((r1_tarski @ sk_B @ sk_A)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.59  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.59  thf(d10_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (![X0 : $i, X2 : $i]:
% 0.37/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('41', plain,
% 0.37/0.59      (((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.37/0.59         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.59  thf('42', plain,
% 0.37/0.59      ((((sk_A) = (sk_B)))
% 0.37/0.59         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.37/0.59             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['28', '41'])).
% 0.37/0.59  thf('43', plain,
% 0.37/0.59      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.37/0.59         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.37/0.59             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.37/0.59  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.37/0.59  thf('45', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_ordinal1 @ X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.37/0.59  thf('46', plain,
% 0.37/0.59      (![X17 : $i, X18 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.59  thf('47', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.37/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.59  thf('48', plain,
% 0.37/0.59      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.59       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['44', '47'])).
% 0.37/0.59  thf('49', plain,
% 0.37/0.59      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.59       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('50', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['5', '48', '49'])).
% 0.37/0.59  thf('51', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['3', '50'])).
% 0.37/0.59  thf('52', plain,
% 0.37/0.59      (![X16 : $i]:
% 0.37/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))),
% 0.37/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.37/0.59  thf('53', plain,
% 0.37/0.59      (![X16 : $i]:
% 0.37/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))),
% 0.37/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.37/0.59  thf(connectedness_r1_ordinal1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.59       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.37/0.59  thf('54', plain,
% 0.37/0.59      (![X3 : $i, X4 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X3)
% 0.37/0.59          | ~ (v3_ordinal1 @ X4)
% 0.37/0.59          | (r1_ordinal1 @ X3 @ X4)
% 0.37/0.59          | (r1_ordinal1 @ X4 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.37/0.59  thf('55', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X6)
% 0.37/0.59          | ~ (v3_ordinal1 @ X7)
% 0.37/0.59          | (r1_tarski @ X6 @ X7)
% 0.37/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.59  thf('56', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((r1_ordinal1 @ X0 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | (r1_tarski @ X1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.59  thf('57', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((r1_tarski @ X1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_ordinal1 @ X0 @ X1))),
% 0.37/0.59      inference('simplify', [status(thm)], ['56'])).
% 0.37/0.59  thf('58', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | (r1_tarski @ X1 @ (k1_ordinal1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['53', '57'])).
% 0.37/0.59  thf('59', plain,
% 0.37/0.59      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.37/0.59         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['4'])).
% 0.37/0.59  thf('60', plain,
% 0.37/0.59      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_A)))
% 0.37/0.59         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.59  thf('61', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('62', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('63', plain,
% 0.37/0.59      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.37/0.59         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.37/0.59  thf(t24_ordinal1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.59           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.37/0.59                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.37/0.59  thf('64', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X12)
% 0.37/0.59          | (r2_hidden @ X13 @ X12)
% 0.37/0.59          | ((X13) = (X12))
% 0.37/0.59          | (r2_hidden @ X12 @ X13)
% 0.37/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.37/0.59  thf('65', plain,
% 0.37/0.59      (![X17 : $i, X18 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.59  thf('66', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X1)
% 0.37/0.59          | (r2_hidden @ X0 @ X1)
% 0.37/0.59          | ((X1) = (X0))
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | ~ (r1_tarski @ X0 @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.37/0.59  thf('67', plain,
% 0.37/0.59      (((~ (v3_ordinal1 @ sk_B)
% 0.37/0.59         | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.37/0.59         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.37/0.59         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.37/0.59         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['63', '66'])).
% 0.37/0.59  thf('68', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('69', plain,
% 0.37/0.59      (((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.37/0.59         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.37/0.59         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.37/0.59         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['67', '68'])).
% 0.37/0.59  thf('70', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['5', '48'])).
% 0.37/0.59  thf('71', plain,
% 0.37/0.59      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.37/0.59        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.37/0.59        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['69', '70'])).
% 0.37/0.59  thf('72', plain,
% 0.37/0.59      ((~ (v3_ordinal1 @ sk_A)
% 0.37/0.59        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.37/0.59        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['52', '71'])).
% 0.37/0.59  thf('73', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('74', plain,
% 0.37/0.59      (((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.37/0.59        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['72', '73'])).
% 0.37/0.59  thf('75', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         (((X10) = (X9))
% 0.37/0.59          | (r2_hidden @ X10 @ X9)
% 0.37/0.59          | ~ (r2_hidden @ X10 @ (k1_ordinal1 @ X9)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.59  thf('76', plain,
% 0.37/0.59      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.37/0.59        | (r2_hidden @ sk_B @ sk_A)
% 0.37/0.59        | ((sk_B) = (sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.37/0.59  thf('77', plain,
% 0.37/0.59      (![X17 : $i, X18 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.59  thf('78', plain,
% 0.37/0.59      ((((sk_B) = (sk_A))
% 0.37/0.59        | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.37/0.59        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.59  thf('79', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((r1_tarski @ X1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_ordinal1 @ X0 @ X1))),
% 0.37/0.59      inference('simplify', [status(thm)], ['56'])).
% 0.37/0.59  thf('80', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X6)
% 0.37/0.59          | ~ (v3_ordinal1 @ X7)
% 0.37/0.59          | (r1_tarski @ X6 @ X7)
% 0.37/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.59  thf('81', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_tarski @ X0 @ X1)
% 0.37/0.59          | (r1_tarski @ X1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['79', '80'])).
% 0.37/0.59  thf('82', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((r1_tarski @ X1 @ X0)
% 0.37/0.59          | (r1_tarski @ X0 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.37/0.59      inference('simplify', [status(thm)], ['81'])).
% 0.37/0.59  thf('83', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['3', '50'])).
% 0.37/0.59  thf('84', plain,
% 0.37/0.59      ((~ (v3_ordinal1 @ sk_B)
% 0.37/0.59        | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.59        | (r1_tarski @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.59  thf('85', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('86', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('87', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.59      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.37/0.59  thf('88', plain, ((((sk_B) = (sk_A)) | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['78', '87'])).
% 0.37/0.59  thf('89', plain,
% 0.37/0.59      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.37/0.59         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['4'])).
% 0.37/0.59  thf('90', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['5', '48'])).
% 0.37/0.59  thf('91', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 0.37/0.59  thf('92', plain, ((~ (r1_ordinal1 @ sk_B @ sk_B) | ((sk_B) = (sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['88', '91'])).
% 0.37/0.59  thf('93', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('94', plain,
% 0.37/0.59      (![X3 : $i, X4 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X3)
% 0.37/0.59          | ~ (v3_ordinal1 @ X4)
% 0.37/0.59          | (r1_ordinal1 @ X3 @ X4)
% 0.37/0.59          | (r1_ordinal1 @ X4 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.37/0.59  thf('95', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((r1_ordinal1 @ X0 @ sk_B)
% 0.37/0.59          | (r1_ordinal1 @ sk_B @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['93', '94'])).
% 0.37/0.59  thf('96', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_B @ sk_B))),
% 0.37/0.59      inference('eq_fact', [status(thm)], ['95'])).
% 0.37/0.59  thf('97', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('98', plain, ((r1_ordinal1 @ sk_B @ sk_B)),
% 0.37/0.59      inference('demod', [status(thm)], ['96', '97'])).
% 0.37/0.59  thf('99', plain, (((sk_B) = (sk_A))),
% 0.37/0.59      inference('demod', [status(thm)], ['92', '98'])).
% 0.37/0.59  thf('100', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('101', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.59      inference('simplify', [status(thm)], ['100'])).
% 0.37/0.59  thf('102', plain, ($false),
% 0.37/0.59      inference('demod', [status(thm)], ['51', '99', '101'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
