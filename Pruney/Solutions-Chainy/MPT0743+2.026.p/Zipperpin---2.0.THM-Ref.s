%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xjRijfkAaU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:56 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 425 expanded)
%              Number of leaves         :   17 ( 122 expanded)
%              Depth                    :   27
%              Number of atoms          :  795 (3550 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
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

thf(fc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( v1_xboole_0 @ ( k1_ordinal1 @ A ) )
        & ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X2 ) )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
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

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ( X12 = X11 )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_ordinal1 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( sk_B = sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('25',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','33'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X2 ) )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X2 ) )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('47',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','31'])).

thf('48',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ( X12 = X11 )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['35','60'])).

thf('62',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( k1_ordinal1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('65',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','31','32'])).

thf('70',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['65','70'])).

thf('72',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['46','47'])).

thf('73',plain,
    ( ~ ( r1_ordinal1 @ sk_B @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_B )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    r1_ordinal1 @ sk_B @ sk_B ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['73','84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('98',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['34','85','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xjRijfkAaU
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 14:53:39 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.38/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.63  % Solved by: fo/fo7.sh
% 0.38/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.63  % done 313 iterations in 0.182s
% 0.38/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.63  % SZS output start Refutation
% 0.38/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.63  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.38/0.63  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.38/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.63  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.38/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.63  thf(t33_ordinal1, conjecture,
% 0.38/0.63    (![A:$i]:
% 0.38/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.38/0.63       ( ![B:$i]:
% 0.38/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.38/0.63           ( ( r2_hidden @ A @ B ) <=>
% 0.38/0.63             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.38/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.63    (~( ![A:$i]:
% 0.38/0.63        ( ( v3_ordinal1 @ A ) =>
% 0.38/0.63          ( ![B:$i]:
% 0.38/0.63            ( ( v3_ordinal1 @ B ) =>
% 0.38/0.63              ( ( r2_hidden @ A @ B ) <=>
% 0.38/0.63                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.38/0.63    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.38/0.63  thf('0', plain,
% 0.38/0.63      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('1', plain,
% 0.38/0.63      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf(t7_ordinal1, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.63  thf('2', plain,
% 0.38/0.63      (![X15 : $i, X16 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.38/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.63  thf('3', plain,
% 0.38/0.63      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.63  thf('4', plain,
% 0.38/0.63      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.38/0.63        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('5', plain,
% 0.38/0.63      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.38/0.63       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.38/0.63      inference('split', [status(esa)], ['4'])).
% 0.38/0.63  thf(fc2_ordinal1, axiom,
% 0.38/0.63    (![A:$i]:
% 0.38/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.38/0.63       ( ( ~( v1_xboole_0 @ ( k1_ordinal1 @ A ) ) ) & 
% 0.38/0.63         ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ))).
% 0.38/0.63  thf('6', plain,
% 0.38/0.63      (![X2 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X2)) | ~ (v3_ordinal1 @ X2))),
% 0.38/0.63      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.38/0.63  thf('7', plain,
% 0.38/0.63      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.38/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf(redefinition_r1_ordinal1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.38/0.63       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.38/0.63  thf('8', plain,
% 0.38/0.63      (![X3 : $i, X4 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X3)
% 0.38/0.63          | ~ (v3_ordinal1 @ X4)
% 0.38/0.63          | (r1_tarski @ X3 @ X4)
% 0.38/0.63          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.38/0.63      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.38/0.63  thf('9', plain,
% 0.38/0.63      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.38/0.63         | ~ (v3_ordinal1 @ sk_B)
% 0.38/0.63         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.38/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.63  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('11', plain,
% 0.38/0.63      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.38/0.63         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.38/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.63  thf('12', plain,
% 0.38/0.63      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.38/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['6', '11'])).
% 0.38/0.63  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('14', plain,
% 0.38/0.63      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.38/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.63  thf(t24_ordinal1, axiom,
% 0.38/0.63    (![A:$i]:
% 0.38/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.38/0.63       ( ![B:$i]:
% 0.38/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.38/0.63           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.38/0.63                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.38/0.63  thf('15', plain,
% 0.38/0.63      (![X11 : $i, X12 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X11)
% 0.38/0.63          | (r2_hidden @ X12 @ X11)
% 0.38/0.63          | ((X12) = (X11))
% 0.38/0.63          | (r2_hidden @ X11 @ X12)
% 0.38/0.63          | ~ (v3_ordinal1 @ X12))),
% 0.38/0.63      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.38/0.63  thf(t13_ordinal1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.38/0.63       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.38/0.63  thf('16', plain,
% 0.38/0.63      (![X9 : $i, X10 : $i]:
% 0.38/0.63         ((r2_hidden @ X9 @ (k1_ordinal1 @ X10)) | ~ (r2_hidden @ X9 @ X10))),
% 0.38/0.63      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.38/0.63  thf('17', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X1)
% 0.38/0.63          | (r2_hidden @ X0 @ X1)
% 0.38/0.63          | ((X1) = (X0))
% 0.38/0.63          | ~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.63  thf('18', plain,
% 0.38/0.63      (![X15 : $i, X16 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.38/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.63  thf('19', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X0)
% 0.38/0.63          | ((X1) = (X0))
% 0.38/0.63          | (r2_hidden @ X0 @ X1)
% 0.38/0.63          | ~ (v3_ordinal1 @ X1)
% 0.38/0.63          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 0.38/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.63  thf('20', plain,
% 0.38/0.63      (((~ (v3_ordinal1 @ sk_B)
% 0.38/0.63         | (r2_hidden @ sk_A @ sk_B)
% 0.38/0.63         | ((sk_B) = (sk_A))
% 0.38/0.63         | ~ (v3_ordinal1 @ sk_A)))
% 0.38/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['14', '19'])).
% 0.38/0.63  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('22', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('23', plain,
% 0.38/0.63      ((((r2_hidden @ sk_A @ sk_B) | ((sk_B) = (sk_A))))
% 0.38/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.38/0.63  thf('24', plain,
% 0.38/0.63      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.63      inference('split', [status(esa)], ['4'])).
% 0.38/0.63  thf('25', plain,
% 0.38/0.63      ((((sk_B) = (sk_A)))
% 0.38/0.63         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.38/0.63             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.63  thf('26', plain,
% 0.38/0.63      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.38/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.63  thf('27', plain,
% 0.38/0.63      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.38/0.63         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.38/0.63             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.38/0.63  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.38/0.63  thf('28', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_ordinal1 @ X7))),
% 0.38/0.63      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.38/0.63  thf('29', plain,
% 0.38/0.63      (![X15 : $i, X16 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.38/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.63  thf('30', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.38/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.63  thf('31', plain,
% 0.38/0.63      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.38/0.63       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.38/0.63      inference('sup-', [status(thm)], ['27', '30'])).
% 0.38/0.63  thf('32', plain,
% 0.38/0.63      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.38/0.63       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf('33', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['5', '31', '32'])).
% 0.38/0.63  thf('34', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['3', '33'])).
% 0.38/0.63  thf('35', plain,
% 0.38/0.63      (![X2 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X2)) | ~ (v3_ordinal1 @ X2))),
% 0.38/0.63      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.38/0.63  thf('36', plain,
% 0.38/0.63      (![X2 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X2)) | ~ (v3_ordinal1 @ X2))),
% 0.38/0.63      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.38/0.63  thf(t26_ordinal1, axiom,
% 0.38/0.63    (![A:$i]:
% 0.38/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.38/0.63       ( ![B:$i]:
% 0.38/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.38/0.63           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.63  thf('37', plain,
% 0.38/0.63      (![X13 : $i, X14 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X13)
% 0.38/0.63          | (r1_ordinal1 @ X14 @ X13)
% 0.38/0.63          | (r2_hidden @ X13 @ X14)
% 0.38/0.63          | ~ (v3_ordinal1 @ X14))),
% 0.38/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.38/0.63  thf('38', plain,
% 0.38/0.63      (![X13 : $i, X14 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X13)
% 0.38/0.63          | (r1_ordinal1 @ X14 @ X13)
% 0.38/0.63          | (r2_hidden @ X13 @ X14)
% 0.38/0.63          | ~ (v3_ordinal1 @ X14))),
% 0.38/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.38/0.63  thf(antisymmetry_r2_hidden, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.38/0.63  thf('39', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.63      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.38/0.63  thf('40', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.38/0.63          | ~ (v3_ordinal1 @ X1)
% 0.38/0.63          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.63  thf('41', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.38/0.63          | ~ (v3_ordinal1 @ X1)
% 0.38/0.63          | ~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r1_ordinal1 @ X1 @ X0)
% 0.38/0.63          | ~ (v3_ordinal1 @ X1))),
% 0.38/0.63      inference('sup-', [status(thm)], ['37', '40'])).
% 0.38/0.63  thf('42', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((r1_ordinal1 @ X1 @ X0)
% 0.38/0.63          | ~ (v3_ordinal1 @ X1)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.38/0.63          | ~ (v3_ordinal1 @ X0))),
% 0.38/0.63      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.63  thf('43', plain,
% 0.38/0.63      (![X3 : $i, X4 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X3)
% 0.38/0.63          | ~ (v3_ordinal1 @ X4)
% 0.38/0.63          | (r1_tarski @ X3 @ X4)
% 0.38/0.63          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.38/0.63      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.38/0.63  thf('44', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.38/0.63          | ~ (v3_ordinal1 @ X1)
% 0.38/0.63          | (r1_tarski @ X1 @ X0)
% 0.38/0.63          | ~ (v3_ordinal1 @ X0)
% 0.38/0.63          | ~ (v3_ordinal1 @ X1))),
% 0.38/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.63  thf('45', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((r1_tarski @ X1 @ X0)
% 0.38/0.63          | ~ (v3_ordinal1 @ X1)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ X1)
% 0.38/0.63          | ~ (v3_ordinal1 @ X0))),
% 0.38/0.63      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.63  thf('46', plain,
% 0.38/0.63      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.38/0.63         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.38/0.63      inference('split', [status(esa)], ['4'])).
% 0.38/0.63  thf('47', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['5', '31'])).
% 0.38/0.63  thf('48', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['46', '47'])).
% 0.38/0.63  thf('49', plain,
% 0.38/0.63      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.38/0.63        | ~ (v3_ordinal1 @ sk_B)
% 0.38/0.63        | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['45', '48'])).
% 0.38/0.63  thf('50', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('51', plain,
% 0.38/0.63      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.38/0.63        | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.38/0.63      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.63  thf('52', plain,
% 0.38/0.63      ((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['36', '51'])).
% 0.38/0.63  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('54', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.63  thf('55', plain,
% 0.38/0.63      (![X11 : $i, X12 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X11)
% 0.38/0.63          | (r2_hidden @ X12 @ X11)
% 0.38/0.63          | ((X12) = (X11))
% 0.38/0.63          | (r2_hidden @ X11 @ X12)
% 0.38/0.63          | ~ (v3_ordinal1 @ X12))),
% 0.38/0.63      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.38/0.63  thf('56', plain,
% 0.38/0.63      (![X15 : $i, X16 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.38/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.63  thf('57', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X1)
% 0.38/0.63          | (r2_hidden @ X0 @ X1)
% 0.38/0.63          | ((X1) = (X0))
% 0.38/0.63          | ~ (v3_ordinal1 @ X0)
% 0.38/0.63          | ~ (r1_tarski @ X0 @ X1))),
% 0.38/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.63  thf('58', plain,
% 0.38/0.63      ((~ (v3_ordinal1 @ sk_B)
% 0.38/0.63        | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.38/0.63        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.38/0.63        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['54', '57'])).
% 0.38/0.63  thf('59', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('60', plain,
% 0.38/0.63      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.38/0.63        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.38/0.63        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.38/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.63  thf('61', plain,
% 0.38/0.63      ((~ (v3_ordinal1 @ sk_A)
% 0.38/0.63        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.38/0.63        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['35', '60'])).
% 0.38/0.63  thf('62', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('63', plain,
% 0.38/0.63      (((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.38/0.63        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.38/0.63      inference('demod', [status(thm)], ['61', '62'])).
% 0.38/0.63  thf('64', plain,
% 0.38/0.63      (![X8 : $i, X9 : $i]:
% 0.38/0.63         (((X9) = (X8))
% 0.38/0.63          | (r2_hidden @ X9 @ X8)
% 0.38/0.63          | ~ (r2_hidden @ X9 @ (k1_ordinal1 @ X8)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.38/0.63  thf('65', plain,
% 0.38/0.63      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.38/0.63        | (r2_hidden @ sk_B @ sk_A)
% 0.38/0.63        | ((sk_B) = (sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.63  thf('66', plain,
% 0.38/0.63      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf('67', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.63      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.38/0.63  thf('68', plain,
% 0.38/0.63      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.63  thf('69', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['5', '31', '32'])).
% 0.38/0.63  thf('70', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.38/0.63  thf('71', plain, ((((sk_B) = (sk_A)) | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.38/0.63      inference('clc', [status(thm)], ['65', '70'])).
% 0.38/0.63  thf('72', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['46', '47'])).
% 0.38/0.63  thf('73', plain, ((~ (r1_ordinal1 @ sk_B @ sk_B) | ((sk_B) = (sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.63  thf('74', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('75', plain,
% 0.38/0.63      (![X13 : $i, X14 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X13)
% 0.38/0.63          | (r1_ordinal1 @ X14 @ X13)
% 0.38/0.63          | (r2_hidden @ X13 @ X14)
% 0.38/0.63          | ~ (v3_ordinal1 @ X14))),
% 0.38/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.38/0.63  thf('76', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r2_hidden @ sk_B @ X0)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ sk_B))),
% 0.38/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.63  thf('77', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r2_hidden @ sk_B @ X0)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ sk_B))),
% 0.38/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.63  thf('78', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.63      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.38/0.63  thf('79', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r1_ordinal1 @ X0 @ sk_B)
% 0.38/0.63          | ~ (v3_ordinal1 @ X0)
% 0.38/0.63          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.63      inference('sup-', [status(thm)], ['77', '78'])).
% 0.38/0.63  thf('80', plain,
% 0.38/0.63      (((r1_ordinal1 @ sk_B @ sk_B)
% 0.38/0.63        | ~ (v3_ordinal1 @ sk_B)
% 0.38/0.63        | ~ (v3_ordinal1 @ sk_B)
% 0.38/0.63        | (r1_ordinal1 @ sk_B @ sk_B))),
% 0.38/0.63      inference('sup-', [status(thm)], ['76', '79'])).
% 0.38/0.63  thf('81', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('82', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('83', plain,
% 0.38/0.63      (((r1_ordinal1 @ sk_B @ sk_B) | (r1_ordinal1 @ sk_B @ sk_B))),
% 0.38/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.38/0.63  thf('84', plain, ((r1_ordinal1 @ sk_B @ sk_B)),
% 0.38/0.63      inference('simplify', [status(thm)], ['83'])).
% 0.38/0.63  thf('85', plain, (((sk_B) = (sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['73', '84'])).
% 0.38/0.63  thf('86', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('87', plain,
% 0.38/0.63      (![X13 : $i, X14 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X13)
% 0.38/0.63          | (r1_ordinal1 @ X14 @ X13)
% 0.38/0.63          | (r2_hidden @ X13 @ X14)
% 0.38/0.63          | ~ (v3_ordinal1 @ X14))),
% 0.38/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.38/0.63  thf('88', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r2_hidden @ sk_A @ X0)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['86', '87'])).
% 0.38/0.63  thf('89', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X0)
% 0.38/0.63          | (r2_hidden @ sk_A @ X0)
% 0.38/0.63          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['86', '87'])).
% 0.38/0.63  thf('90', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.63      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.38/0.63  thf('91', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r1_ordinal1 @ X0 @ sk_A)
% 0.38/0.63          | ~ (v3_ordinal1 @ X0)
% 0.38/0.63          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.63  thf('92', plain,
% 0.38/0.63      (((r1_ordinal1 @ sk_A @ sk_A)
% 0.38/0.63        | ~ (v3_ordinal1 @ sk_A)
% 0.38/0.63        | ~ (v3_ordinal1 @ sk_A)
% 0.38/0.63        | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['88', '91'])).
% 0.38/0.63  thf('93', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('94', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('95', plain,
% 0.38/0.63      (((r1_ordinal1 @ sk_A @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.38/0.63  thf('96', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.38/0.63      inference('simplify', [status(thm)], ['95'])).
% 0.38/0.63  thf('97', plain,
% 0.38/0.63      (![X3 : $i, X4 : $i]:
% 0.38/0.63         (~ (v3_ordinal1 @ X3)
% 0.38/0.63          | ~ (v3_ordinal1 @ X4)
% 0.38/0.63          | (r1_tarski @ X3 @ X4)
% 0.38/0.63          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.38/0.63      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.38/0.63  thf('98', plain,
% 0.38/0.63      (((r1_tarski @ sk_A @ sk_A)
% 0.38/0.63        | ~ (v3_ordinal1 @ sk_A)
% 0.38/0.63        | ~ (v3_ordinal1 @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['96', '97'])).
% 0.38/0.63  thf('99', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('100', plain, ((v3_ordinal1 @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('101', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.38/0.63      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.38/0.63  thf('102', plain, ($false),
% 0.38/0.63      inference('demod', [status(thm)], ['34', '85', '101'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.38/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
