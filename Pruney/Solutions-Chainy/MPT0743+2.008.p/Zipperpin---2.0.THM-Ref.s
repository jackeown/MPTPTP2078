%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ixHpqkfZzr

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:53 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 526 expanded)
%              Number of leaves         :   16 ( 151 expanded)
%              Depth                    :   34
%              Number of atoms          :  797 (4321 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
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
    ! [X51: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X51 ) )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
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
    ! [X49: $i,X50: $i] :
      ( ~ ( v3_ordinal1 @ X49 )
      | ( r1_ordinal1 @ X50 @ X49 )
      | ( r2_hidden @ X49 @ X50 )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('16',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ X45 @ ( k1_ordinal1 @ X46 ) )
      | ~ ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
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
    ! [X49: $i,X50: $i] :
      ( ~ ( v3_ordinal1 @ X49 )
      | ( r1_ordinal1 @ X50 @ X49 )
      | ( r2_hidden @ X49 @ X50 )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
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
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
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

thf('45',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ X45 @ ( k1_ordinal1 @ X46 ) )
      | ( X45 != X46 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('46',plain,(
    ! [X46: $i] :
      ( r2_hidden @ X46 @ ( k1_ordinal1 @ X46 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','49','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_ordinal1 @ X42 @ X43 )
      | ~ ( r1_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X51: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X51 ) )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('59',plain,(
    ! [X51: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X51 ) )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('60',plain,(
    ! [X51: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X51 ) )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('61',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v3_ordinal1 @ X49 )
      | ( r1_ordinal1 @ X50 @ X49 )
      | ( r2_hidden @ X49 @ X50 )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('62',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v3_ordinal1 @ X49 )
      | ( r1_ordinal1 @ X50 @ X49 )
      | ( r2_hidden @ X49 @ X50 )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('68',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','49'])).

thf('69',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('77',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','79'])).

thf('81',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('83',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ( r2_hidden @ X48 @ X47 )
      | ( X48 = X47 )
      | ( r2_hidden @ X47 @ X48 )
      | ~ ( v3_ordinal1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('84',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['58','88'])).

thf('90',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45 = X44 )
      | ( r2_hidden @ X45 @ X44 )
      | ~ ( r2_hidden @ X45 @ ( k1_ordinal1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('93',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('96',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','49','50'])).

thf('98',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['93','98'])).

thf('100',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['67','68'])).

thf('101',plain,
    ( ~ ( r1_ordinal1 @ sk_B @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['57','101'])).

thf('103',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['52','104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ixHpqkfZzr
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.39/1.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.39/1.60  % Solved by: fo/fo7.sh
% 1.39/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.39/1.60  % done 2629 iterations in 1.145s
% 1.39/1.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.39/1.60  % SZS output start Refutation
% 1.39/1.60  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.39/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.39/1.60  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.39/1.60  thf(sk_B_type, type, sk_B: $i).
% 1.39/1.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.39/1.60  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.39/1.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.39/1.60  thf(t33_ordinal1, conjecture,
% 1.39/1.60    (![A:$i]:
% 1.39/1.60     ( ( v3_ordinal1 @ A ) =>
% 1.39/1.60       ( ![B:$i]:
% 1.39/1.60         ( ( v3_ordinal1 @ B ) =>
% 1.39/1.60           ( ( r2_hidden @ A @ B ) <=>
% 1.39/1.60             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 1.39/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.39/1.60    (~( ![A:$i]:
% 1.39/1.60        ( ( v3_ordinal1 @ A ) =>
% 1.39/1.60          ( ![B:$i]:
% 1.39/1.60            ( ( v3_ordinal1 @ B ) =>
% 1.39/1.60              ( ( r2_hidden @ A @ B ) <=>
% 1.39/1.60                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 1.39/1.60    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 1.39/1.60  thf('0', plain,
% 1.39/1.60      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('1', plain,
% 1.39/1.60      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('split', [status(esa)], ['0'])).
% 1.39/1.60  thf(t7_ordinal1, axiom,
% 1.39/1.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.39/1.60  thf('2', plain,
% 1.39/1.60      (![X52 : $i, X53 : $i]:
% 1.39/1.60         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 1.39/1.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.39/1.60  thf('3', plain,
% 1.39/1.60      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['1', '2'])).
% 1.39/1.60  thf('4', plain,
% 1.39/1.60      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.39/1.60        | ~ (r2_hidden @ sk_A @ sk_B))),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('5', plain,
% 1.39/1.60      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 1.39/1.60       ~ ((r2_hidden @ sk_A @ sk_B))),
% 1.39/1.60      inference('split', [status(esa)], ['4'])).
% 1.39/1.60  thf(t29_ordinal1, axiom,
% 1.39/1.60    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 1.39/1.60  thf('6', plain,
% 1.39/1.60      (![X51 : $i]:
% 1.39/1.60         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 1.39/1.60      inference('cnf', [status(esa)], [t29_ordinal1])).
% 1.39/1.60  thf('7', plain,
% 1.39/1.60      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('split', [status(esa)], ['0'])).
% 1.39/1.60  thf(redefinition_r1_ordinal1, axiom,
% 1.39/1.60    (![A:$i,B:$i]:
% 1.39/1.60     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.39/1.60       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.39/1.60  thf('8', plain,
% 1.39/1.60      (![X42 : $i, X43 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X42)
% 1.39/1.60          | ~ (v3_ordinal1 @ X43)
% 1.39/1.60          | (r1_tarski @ X42 @ X43)
% 1.39/1.60          | ~ (r1_ordinal1 @ X42 @ X43))),
% 1.39/1.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.39/1.60  thf('9', plain,
% 1.39/1.60      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.39/1.60         | ~ (v3_ordinal1 @ sk_B)
% 1.39/1.60         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['7', '8'])).
% 1.39/1.60  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('11', plain,
% 1.39/1.60      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.39/1.60         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('demod', [status(thm)], ['9', '10'])).
% 1.39/1.60  thf('12', plain,
% 1.39/1.60      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['6', '11'])).
% 1.39/1.60  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('14', plain,
% 1.39/1.60      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('demod', [status(thm)], ['12', '13'])).
% 1.39/1.60  thf(t26_ordinal1, axiom,
% 1.39/1.60    (![A:$i]:
% 1.39/1.60     ( ( v3_ordinal1 @ A ) =>
% 1.39/1.60       ( ![B:$i]:
% 1.39/1.60         ( ( v3_ordinal1 @ B ) =>
% 1.39/1.60           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 1.39/1.60  thf('15', plain,
% 1.39/1.60      (![X49 : $i, X50 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X49)
% 1.39/1.60          | (r1_ordinal1 @ X50 @ X49)
% 1.39/1.60          | (r2_hidden @ X49 @ X50)
% 1.39/1.60          | ~ (v3_ordinal1 @ X50))),
% 1.39/1.60      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.39/1.60  thf(t13_ordinal1, axiom,
% 1.39/1.60    (![A:$i,B:$i]:
% 1.39/1.60     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.39/1.60       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 1.39/1.60  thf('16', plain,
% 1.39/1.60      (![X45 : $i, X46 : $i]:
% 1.39/1.60         ((r2_hidden @ X45 @ (k1_ordinal1 @ X46)) | ~ (r2_hidden @ X45 @ X46))),
% 1.39/1.60      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.39/1.60  thf('17', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X0)
% 1.39/1.60          | (r1_ordinal1 @ X0 @ X1)
% 1.39/1.60          | ~ (v3_ordinal1 @ X1)
% 1.39/1.60          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['15', '16'])).
% 1.39/1.60  thf('18', plain,
% 1.39/1.60      (![X52 : $i, X53 : $i]:
% 1.39/1.60         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 1.39/1.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.39/1.60  thf('19', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X1)
% 1.39/1.60          | (r1_ordinal1 @ X0 @ X1)
% 1.39/1.60          | ~ (v3_ordinal1 @ X0)
% 1.39/1.60          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 1.39/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.39/1.60  thf('20', plain,
% 1.39/1.60      (((~ (v3_ordinal1 @ sk_A)
% 1.39/1.60         | (r1_ordinal1 @ sk_A @ sk_B)
% 1.39/1.60         | ~ (v3_ordinal1 @ sk_B)))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['14', '19'])).
% 1.39/1.60  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('23', plain,
% 1.39/1.60      (((r1_ordinal1 @ sk_A @ sk_B))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.39/1.60  thf('24', plain,
% 1.39/1.60      (![X42 : $i, X43 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X42)
% 1.39/1.60          | ~ (v3_ordinal1 @ X43)
% 1.39/1.60          | (r1_tarski @ X42 @ X43)
% 1.39/1.60          | ~ (r1_ordinal1 @ X42 @ X43))),
% 1.39/1.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.39/1.60  thf('25', plain,
% 1.39/1.60      ((((r1_tarski @ sk_A @ sk_B)
% 1.39/1.60         | ~ (v3_ordinal1 @ sk_B)
% 1.39/1.60         | ~ (v3_ordinal1 @ sk_A)))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['23', '24'])).
% 1.39/1.60  thf('26', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('28', plain,
% 1.39/1.60      (((r1_tarski @ sk_A @ sk_B))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.39/1.60  thf('29', plain,
% 1.39/1.60      (![X49 : $i, X50 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X49)
% 1.39/1.60          | (r1_ordinal1 @ X50 @ X49)
% 1.39/1.60          | (r2_hidden @ X49 @ X50)
% 1.39/1.60          | ~ (v3_ordinal1 @ X50))),
% 1.39/1.60      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.39/1.60  thf('30', plain,
% 1.39/1.60      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('split', [status(esa)], ['4'])).
% 1.39/1.60  thf('31', plain,
% 1.39/1.60      (((~ (v3_ordinal1 @ sk_B)
% 1.39/1.60         | (r1_ordinal1 @ sk_B @ sk_A)
% 1.39/1.60         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['29', '30'])).
% 1.39/1.60  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('34', plain,
% 1.39/1.60      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.39/1.60  thf('35', plain,
% 1.39/1.60      (![X42 : $i, X43 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X42)
% 1.39/1.60          | ~ (v3_ordinal1 @ X43)
% 1.39/1.60          | (r1_tarski @ X42 @ X43)
% 1.39/1.60          | ~ (r1_ordinal1 @ X42 @ X43))),
% 1.39/1.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.39/1.60  thf('36', plain,
% 1.39/1.60      ((((r1_tarski @ sk_B @ sk_A)
% 1.39/1.60         | ~ (v3_ordinal1 @ sk_A)
% 1.39/1.60         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['34', '35'])).
% 1.39/1.60  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('39', plain,
% 1.39/1.60      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.39/1.60  thf(d10_xboole_0, axiom,
% 1.39/1.60    (![A:$i,B:$i]:
% 1.39/1.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.39/1.60  thf('40', plain,
% 1.39/1.60      (![X8 : $i, X10 : $i]:
% 1.39/1.60         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.39/1.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.39/1.60  thf('41', plain,
% 1.39/1.60      (((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 1.39/1.60         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['39', '40'])).
% 1.39/1.60  thf('42', plain,
% 1.39/1.60      ((((sk_A) = (sk_B)))
% 1.39/1.60         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 1.39/1.60             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['28', '41'])).
% 1.39/1.60  thf('43', plain,
% 1.39/1.60      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.39/1.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('demod', [status(thm)], ['12', '13'])).
% 1.39/1.60  thf('44', plain,
% 1.39/1.60      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 1.39/1.60         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 1.39/1.60             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('sup+', [status(thm)], ['42', '43'])).
% 1.39/1.60  thf('45', plain,
% 1.39/1.60      (![X45 : $i, X46 : $i]:
% 1.39/1.60         ((r2_hidden @ X45 @ (k1_ordinal1 @ X46)) | ((X45) != (X46)))),
% 1.39/1.60      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.39/1.60  thf('46', plain, (![X46 : $i]: (r2_hidden @ X46 @ (k1_ordinal1 @ X46))),
% 1.39/1.60      inference('simplify', [status(thm)], ['45'])).
% 1.39/1.60  thf('47', plain,
% 1.39/1.60      (![X52 : $i, X53 : $i]:
% 1.39/1.60         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 1.39/1.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.39/1.60  thf('48', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 1.39/1.60      inference('sup-', [status(thm)], ['46', '47'])).
% 1.39/1.60  thf('49', plain,
% 1.39/1.60      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.39/1.60       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.39/1.60      inference('sup-', [status(thm)], ['44', '48'])).
% 1.39/1.60  thf('50', plain,
% 1.39/1.60      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.39/1.60       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.39/1.60      inference('split', [status(esa)], ['0'])).
% 1.39/1.60  thf('51', plain, (((r2_hidden @ sk_A @ sk_B))),
% 1.39/1.60      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 1.39/1.60  thf('52', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 1.39/1.60      inference('simpl_trail', [status(thm)], ['3', '51'])).
% 1.39/1.60  thf('53', plain,
% 1.39/1.60      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.39/1.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.39/1.60  thf('54', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.39/1.60      inference('simplify', [status(thm)], ['53'])).
% 1.39/1.60  thf('55', plain,
% 1.39/1.60      (![X42 : $i, X43 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X42)
% 1.39/1.60          | ~ (v3_ordinal1 @ X43)
% 1.39/1.60          | (r1_ordinal1 @ X42 @ X43)
% 1.39/1.60          | ~ (r1_tarski @ X42 @ X43))),
% 1.39/1.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.39/1.60  thf('56', plain,
% 1.39/1.60      (![X0 : $i]:
% 1.39/1.60         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 1.39/1.60      inference('sup-', [status(thm)], ['54', '55'])).
% 1.39/1.60  thf('57', plain,
% 1.39/1.60      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 1.39/1.60      inference('simplify', [status(thm)], ['56'])).
% 1.39/1.60  thf('58', plain,
% 1.39/1.60      (![X51 : $i]:
% 1.39/1.60         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 1.39/1.60      inference('cnf', [status(esa)], [t29_ordinal1])).
% 1.39/1.60  thf('59', plain,
% 1.39/1.60      (![X51 : $i]:
% 1.39/1.60         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 1.39/1.60      inference('cnf', [status(esa)], [t29_ordinal1])).
% 1.39/1.60  thf('60', plain,
% 1.39/1.60      (![X51 : $i]:
% 1.39/1.60         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 1.39/1.60      inference('cnf', [status(esa)], [t29_ordinal1])).
% 1.39/1.60  thf('61', plain,
% 1.39/1.60      (![X49 : $i, X50 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X49)
% 1.39/1.60          | (r1_ordinal1 @ X50 @ X49)
% 1.39/1.60          | (r2_hidden @ X49 @ X50)
% 1.39/1.60          | ~ (v3_ordinal1 @ X50))),
% 1.39/1.60      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.39/1.60  thf('62', plain,
% 1.39/1.60      (![X49 : $i, X50 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X49)
% 1.39/1.60          | (r1_ordinal1 @ X50 @ X49)
% 1.39/1.60          | (r2_hidden @ X49 @ X50)
% 1.39/1.60          | ~ (v3_ordinal1 @ X50))),
% 1.39/1.60      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.39/1.60  thf(antisymmetry_r2_hidden, axiom,
% 1.39/1.60    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 1.39/1.60  thf('63', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.39/1.60      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.39/1.60  thf('64', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X0)
% 1.39/1.60          | (r1_ordinal1 @ X0 @ X1)
% 1.39/1.60          | ~ (v3_ordinal1 @ X1)
% 1.39/1.60          | ~ (r2_hidden @ X0 @ X1))),
% 1.39/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.39/1.60  thf('65', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X0)
% 1.39/1.60          | (r1_ordinal1 @ X0 @ X1)
% 1.39/1.60          | ~ (v3_ordinal1 @ X1)
% 1.39/1.60          | ~ (v3_ordinal1 @ X0)
% 1.39/1.60          | (r1_ordinal1 @ X1 @ X0)
% 1.39/1.60          | ~ (v3_ordinal1 @ X1))),
% 1.39/1.60      inference('sup-', [status(thm)], ['61', '64'])).
% 1.39/1.60  thf('66', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         ((r1_ordinal1 @ X1 @ X0)
% 1.39/1.60          | ~ (v3_ordinal1 @ X1)
% 1.39/1.60          | (r1_ordinal1 @ X0 @ X1)
% 1.39/1.60          | ~ (v3_ordinal1 @ X0))),
% 1.39/1.60      inference('simplify', [status(thm)], ['65'])).
% 1.39/1.60  thf('67', plain,
% 1.39/1.60      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.39/1.60         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.39/1.60      inference('split', [status(esa)], ['4'])).
% 1.39/1.60  thf('68', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.39/1.60      inference('sat_resolution*', [status(thm)], ['5', '49'])).
% 1.39/1.60  thf('69', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 1.39/1.60      inference('simpl_trail', [status(thm)], ['67', '68'])).
% 1.39/1.60  thf('70', plain,
% 1.39/1.60      ((~ (v3_ordinal1 @ sk_B)
% 1.39/1.60        | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['66', '69'])).
% 1.39/1.60  thf('71', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('72', plain,
% 1.39/1.60      (((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 1.39/1.60      inference('demod', [status(thm)], ['70', '71'])).
% 1.39/1.60  thf('73', plain,
% 1.39/1.60      ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['60', '72'])).
% 1.39/1.60  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('75', plain, ((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))),
% 1.39/1.60      inference('demod', [status(thm)], ['73', '74'])).
% 1.39/1.60  thf('76', plain,
% 1.39/1.60      (![X42 : $i, X43 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X42)
% 1.39/1.60          | ~ (v3_ordinal1 @ X43)
% 1.39/1.60          | (r1_tarski @ X42 @ X43)
% 1.39/1.60          | ~ (r1_ordinal1 @ X42 @ X43))),
% 1.39/1.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.39/1.60  thf('77', plain,
% 1.39/1.60      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ~ (v3_ordinal1 @ sk_B))),
% 1.39/1.60      inference('sup-', [status(thm)], ['75', '76'])).
% 1.39/1.60  thf('78', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('79', plain,
% 1.39/1.60      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 1.39/1.60      inference('demod', [status(thm)], ['77', '78'])).
% 1.39/1.60  thf('80', plain,
% 1.39/1.60      ((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['59', '79'])).
% 1.39/1.60  thf('81', plain, ((v3_ordinal1 @ sk_A)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('82', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 1.39/1.60      inference('demod', [status(thm)], ['80', '81'])).
% 1.39/1.60  thf(t24_ordinal1, axiom,
% 1.39/1.60    (![A:$i]:
% 1.39/1.60     ( ( v3_ordinal1 @ A ) =>
% 1.39/1.60       ( ![B:$i]:
% 1.39/1.60         ( ( v3_ordinal1 @ B ) =>
% 1.39/1.60           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 1.39/1.60                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 1.39/1.60  thf('83', plain,
% 1.39/1.60      (![X47 : $i, X48 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X47)
% 1.39/1.60          | (r2_hidden @ X48 @ X47)
% 1.39/1.60          | ((X48) = (X47))
% 1.39/1.60          | (r2_hidden @ X47 @ X48)
% 1.39/1.60          | ~ (v3_ordinal1 @ X48))),
% 1.39/1.60      inference('cnf', [status(esa)], [t24_ordinal1])).
% 1.39/1.60  thf('84', plain,
% 1.39/1.60      (![X52 : $i, X53 : $i]:
% 1.39/1.60         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 1.39/1.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.39/1.60  thf('85', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]:
% 1.39/1.60         (~ (v3_ordinal1 @ X1)
% 1.39/1.60          | (r2_hidden @ X0 @ X1)
% 1.39/1.60          | ((X1) = (X0))
% 1.39/1.60          | ~ (v3_ordinal1 @ X0)
% 1.39/1.60          | ~ (r1_tarski @ X0 @ X1))),
% 1.39/1.60      inference('sup-', [status(thm)], ['83', '84'])).
% 1.39/1.60  thf('86', plain,
% 1.39/1.60      ((~ (v3_ordinal1 @ sk_B)
% 1.39/1.60        | ((k1_ordinal1 @ sk_A) = (sk_B))
% 1.39/1.60        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['82', '85'])).
% 1.39/1.60  thf('87', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('88', plain,
% 1.39/1.60      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 1.39/1.60        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 1.39/1.60      inference('demod', [status(thm)], ['86', '87'])).
% 1.39/1.60  thf('89', plain,
% 1.39/1.60      ((~ (v3_ordinal1 @ sk_A)
% 1.39/1.60        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['58', '88'])).
% 1.39/1.60  thf('90', plain, ((v3_ordinal1 @ sk_A)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('91', plain,
% 1.39/1.60      (((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 1.39/1.60        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 1.39/1.60      inference('demod', [status(thm)], ['89', '90'])).
% 1.39/1.60  thf('92', plain,
% 1.39/1.60      (![X44 : $i, X45 : $i]:
% 1.39/1.60         (((X45) = (X44))
% 1.39/1.60          | (r2_hidden @ X45 @ X44)
% 1.39/1.60          | ~ (r2_hidden @ X45 @ (k1_ordinal1 @ X44)))),
% 1.39/1.60      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.39/1.60  thf('93', plain,
% 1.39/1.60      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 1.39/1.60        | (r2_hidden @ sk_B @ sk_A)
% 1.39/1.60        | ((sk_B) = (sk_A)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['91', '92'])).
% 1.39/1.60  thf('94', plain,
% 1.39/1.60      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('split', [status(esa)], ['0'])).
% 1.39/1.60  thf('95', plain,
% 1.39/1.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.39/1.60      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.39/1.60  thf('96', plain,
% 1.39/1.60      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['94', '95'])).
% 1.39/1.60  thf('97', plain, (((r2_hidden @ sk_A @ sk_B))),
% 1.39/1.60      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 1.39/1.60  thf('98', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.39/1.60      inference('simpl_trail', [status(thm)], ['96', '97'])).
% 1.39/1.60  thf('99', plain, ((((sk_B) = (sk_A)) | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 1.39/1.60      inference('clc', [status(thm)], ['93', '98'])).
% 1.39/1.60  thf('100', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 1.39/1.60      inference('simpl_trail', [status(thm)], ['67', '68'])).
% 1.39/1.60  thf('101', plain, ((~ (r1_ordinal1 @ sk_B @ sk_B) | ((sk_B) = (sk_A)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['99', '100'])).
% 1.39/1.60  thf('102', plain, ((~ (v3_ordinal1 @ sk_B) | ((sk_B) = (sk_A)))),
% 1.39/1.60      inference('sup-', [status(thm)], ['57', '101'])).
% 1.39/1.60  thf('103', plain, ((v3_ordinal1 @ sk_B)),
% 1.39/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.60  thf('104', plain, (((sk_B) = (sk_A))),
% 1.39/1.60      inference('demod', [status(thm)], ['102', '103'])).
% 1.39/1.60  thf('105', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.39/1.60      inference('simplify', [status(thm)], ['53'])).
% 1.39/1.60  thf('106', plain, ($false),
% 1.39/1.60      inference('demod', [status(thm)], ['52', '104', '105'])).
% 1.39/1.60  
% 1.39/1.60  % SZS output end Refutation
% 1.39/1.60  
% 1.39/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
