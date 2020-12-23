%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Yrwx4aoUs

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:57 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 872 expanded)
%              Number of leaves         :   16 ( 251 expanded)
%              Depth                    :   25
%              Number of atoms          : 1022 (7482 expanded)
%              Number of equality atoms :   38 ( 165 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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

thf('16',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('22',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ( r2_hidden @ X48 @ X47 )
      | ( X48 = X47 )
      | ( r2_hidden @ X47 @ X48 )
      | ~ ( v3_ordinal1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('27',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('33',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ X45 @ ( k1_ordinal1 @ X46 ) )
      | ~ ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('34',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('36',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','36'])).

thf('38',plain,(
    ! [X51: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X51 ) )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('39',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('41',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ X45 @ ( k1_ordinal1 @ X46 ) )
      | ~ ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('48',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ ( k1_ordinal1 @ sk_B ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ sk_B ) @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','36'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','53','54'])).

thf('56',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r2_hidden @ X45 @ ( k1_ordinal1 @ X46 ) )
      | ( X45 != X46 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('57',plain,(
    ! [X46: $i] :
      ( r2_hidden @ X46 @ ( k1_ordinal1 @ X46 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('62',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','62','63'])).

thf('65',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','64'])).

thf('66',plain,(
    ! [X51: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X51 ) )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('67',plain,(
    ! [X51: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X51 ) )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('68',plain,(
    ! [X51: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X51 ) )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v3_ordinal1 @ X39 )
      | ~ ( v3_ordinal1 @ X40 )
      | ( r1_ordinal1 @ X39 @ X40 )
      | ( r1_ordinal1 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('70',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('71',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('78',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['67','80'])).

thf('82',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('85',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( ( k1_ordinal1 @ sk_A )
        = sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','87'])).

thf('89',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45 = X44 )
      | ( r2_hidden @ X45 @ X44 )
      | ~ ( r2_hidden @ X45 @ ( k1_ordinal1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('92',plain,
    ( ( ( ( k1_ordinal1 @ sk_A )
        = sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','62'])).

thf('94',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('96',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v3_ordinal1 @ X39 )
      | ~ ( v3_ordinal1 @ X40 )
      | ( r1_ordinal1 @ X39 @ X40 )
      | ( r1_ordinal1 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('98',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','64'])).

thf('105',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['96','108'])).

thf('110',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('111',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','62'])).

thf('112',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r1_ordinal1 @ sk_B @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v3_ordinal1 @ X39 )
      | ~ ( v3_ordinal1 @ X40 )
      | ( r1_ordinal1 @ X39 @ X40 )
      | ( r1_ordinal1 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_B ) ),
    inference(eq_fact,[status(thm)],['116'])).

thf('118',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    r1_ordinal1 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['113','119'])).

thf('121',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['65','120','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Yrwx4aoUs
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.12  % Solved by: fo/fo7.sh
% 0.90/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.12  % done 1505 iterations in 0.660s
% 0.90/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.12  % SZS output start Refutation
% 0.90/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.12  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.90/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.12  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.90/1.12  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.90/1.12  thf(t33_ordinal1, conjecture,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v3_ordinal1 @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( v3_ordinal1 @ B ) =>
% 0.90/1.12           ( ( r2_hidden @ A @ B ) <=>
% 0.90/1.12             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.12    (~( ![A:$i]:
% 0.90/1.12        ( ( v3_ordinal1 @ A ) =>
% 0.90/1.12          ( ![B:$i]:
% 0.90/1.12            ( ( v3_ordinal1 @ B ) =>
% 0.90/1.12              ( ( r2_hidden @ A @ B ) <=>
% 0.90/1.12                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.90/1.12    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.90/1.12  thf('0', plain,
% 0.90/1.12      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('1', plain,
% 0.90/1.12      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf(t7_ordinal1, axiom,
% 0.90/1.12    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.12  thf('2', plain,
% 0.90/1.12      (![X52 : $i, X53 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.90/1.12      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.90/1.12  thf('3', plain,
% 0.90/1.12      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.12  thf('4', plain,
% 0.90/1.12      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.90/1.12        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('5', plain,
% 0.90/1.12      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.90/1.12       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.90/1.12      inference('split', [status(esa)], ['4'])).
% 0.90/1.12  thf(t29_ordinal1, axiom,
% 0.90/1.12    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.90/1.12  thf('6', plain,
% 0.90/1.12      (![X51 : $i]:
% 0.90/1.12         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 0.90/1.12      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.90/1.12  thf('7', plain,
% 0.90/1.12      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf(redefinition_r1_ordinal1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.90/1.12       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.90/1.12  thf('8', plain,
% 0.90/1.12      (![X42 : $i, X43 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X42)
% 0.90/1.12          | ~ (v3_ordinal1 @ X43)
% 0.90/1.12          | (r1_tarski @ X42 @ X43)
% 0.90/1.12          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.90/1.12  thf('9', plain,
% 0.90/1.12      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.90/1.12         | ~ (v3_ordinal1 @ sk_B)
% 0.90/1.12         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.12  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('11', plain,
% 0.90/1.12      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.90/1.12         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['9', '10'])).
% 0.90/1.12  thf('12', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['6', '11'])).
% 0.90/1.12  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('14', plain,
% 0.90/1.12      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['12', '13'])).
% 0.90/1.12  thf(t26_ordinal1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v3_ordinal1 @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( v3_ordinal1 @ B ) =>
% 0.90/1.12           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.90/1.12  thf('15', plain,
% 0.90/1.12      (![X49 : $i, X50 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X49)
% 0.90/1.12          | (r1_ordinal1 @ X50 @ X49)
% 0.90/1.12          | (r2_hidden @ X49 @ X50)
% 0.90/1.12          | ~ (v3_ordinal1 @ X50))),
% 0.90/1.12      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.90/1.12  thf('16', plain,
% 0.90/1.12      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('split', [status(esa)], ['4'])).
% 0.90/1.12  thf('17', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ sk_B)
% 0.90/1.12         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.90/1.12         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['15', '16'])).
% 0.90/1.12  thf('18', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('19', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('20', plain,
% 0.90/1.12      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.90/1.12  thf('21', plain,
% 0.90/1.12      (![X42 : $i, X43 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X42)
% 0.90/1.12          | ~ (v3_ordinal1 @ X43)
% 0.90/1.12          | (r1_tarski @ X42 @ X43)
% 0.90/1.12          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.90/1.12  thf('22', plain,
% 0.90/1.12      ((((r1_tarski @ sk_B @ sk_A)
% 0.90/1.12         | ~ (v3_ordinal1 @ sk_A)
% 0.90/1.12         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.12  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('24', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('25', plain,
% 0.90/1.12      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.90/1.12  thf(t24_ordinal1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v3_ordinal1 @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( v3_ordinal1 @ B ) =>
% 0.90/1.12           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.90/1.12                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.90/1.12  thf('26', plain,
% 0.90/1.12      (![X47 : $i, X48 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X47)
% 0.90/1.12          | (r2_hidden @ X48 @ X47)
% 0.90/1.12          | ((X48) = (X47))
% 0.90/1.12          | (r2_hidden @ X47 @ X48)
% 0.90/1.12          | ~ (v3_ordinal1 @ X48))),
% 0.90/1.12      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.90/1.12  thf('27', plain,
% 0.90/1.12      (![X52 : $i, X53 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.90/1.12      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.90/1.12  thf('28', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X1)
% 0.90/1.12          | (r2_hidden @ X0 @ X1)
% 0.90/1.12          | ((X1) = (X0))
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | ~ (r1_tarski @ X0 @ X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.12  thf('29', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ sk_B)
% 0.90/1.12         | ((sk_A) = (sk_B))
% 0.90/1.12         | (r2_hidden @ sk_B @ sk_A)
% 0.90/1.12         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['25', '28'])).
% 0.90/1.12  thf('30', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('32', plain,
% 0.90/1.12      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_A)))
% 0.90/1.12         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.90/1.12  thf(t13_ordinal1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.90/1.12       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.90/1.12  thf('33', plain,
% 0.90/1.12      (![X45 : $i, X46 : $i]:
% 0.90/1.12         ((r2_hidden @ X45 @ (k1_ordinal1 @ X46)) | ~ (r2_hidden @ X45 @ X46))),
% 0.90/1.12      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.90/1.12  thf('34', plain,
% 0.90/1.12      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['32', '33'])).
% 0.90/1.12  thf('35', plain,
% 0.90/1.12      (![X52 : $i, X53 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.90/1.12      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.90/1.12  thf('36', plain,
% 0.90/1.12      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.90/1.12         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.12  thf('37', plain,
% 0.90/1.12      ((((sk_A) = (sk_B)))
% 0.90/1.12         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.90/1.12             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['14', '36'])).
% 0.90/1.12  thf('38', plain,
% 0.90/1.12      (![X51 : $i]:
% 0.90/1.12         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 0.90/1.12      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.90/1.12  thf('39', plain,
% 0.90/1.12      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['12', '13'])).
% 0.90/1.12  thf('40', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X1)
% 0.90/1.12          | (r2_hidden @ X0 @ X1)
% 0.90/1.12          | ((X1) = (X0))
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | ~ (r1_tarski @ X0 @ X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.12  thf('41', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 0.90/1.12         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.90/1.12         | ~ (v3_ordinal1 @ sk_B)))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['39', '40'])).
% 0.90/1.12  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('43', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 0.90/1.12         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['41', '42'])).
% 0.90/1.12  thf('44', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ sk_A)
% 0.90/1.12         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.90/1.12         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['38', '43'])).
% 0.90/1.12  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('46', plain,
% 0.90/1.12      ((((r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.90/1.12         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['44', '45'])).
% 0.90/1.12  thf('47', plain,
% 0.90/1.12      (![X45 : $i, X46 : $i]:
% 0.90/1.12         ((r2_hidden @ X45 @ (k1_ordinal1 @ X46)) | ~ (r2_hidden @ X45 @ X46))),
% 0.90/1.12      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.90/1.12  thf('48', plain,
% 0.90/1.12      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.90/1.12         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ (k1_ordinal1 @ sk_B))))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['46', '47'])).
% 0.90/1.12  thf('49', plain,
% 0.90/1.12      (![X52 : $i, X53 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.90/1.12      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.90/1.12  thf('50', plain,
% 0.90/1.12      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ~ (r1_tarski @ (k1_ordinal1 @ sk_B) @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['48', '49'])).
% 0.90/1.12  thf('51', plain,
% 0.90/1.12      (((~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.90/1.12             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['37', '50'])).
% 0.90/1.12  thf(d10_xboole_0, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.12  thf('52', plain,
% 0.90/1.12      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.90/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.12  thf('53', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.90/1.12      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.12  thf('54', plain,
% 0.90/1.12      ((((sk_A) = (sk_B)))
% 0.90/1.12         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.90/1.12             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['14', '36'])).
% 0.90/1.12  thf('55', plain,
% 0.90/1.12      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.90/1.12         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.90/1.12             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['51', '53', '54'])).
% 0.90/1.12  thf('56', plain,
% 0.90/1.12      (![X45 : $i, X46 : $i]:
% 0.90/1.12         ((r2_hidden @ X45 @ (k1_ordinal1 @ X46)) | ((X45) != (X46)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.90/1.12  thf('57', plain, (![X46 : $i]: (r2_hidden @ X46 @ (k1_ordinal1 @ X46))),
% 0.90/1.12      inference('simplify', [status(thm)], ['56'])).
% 0.90/1.12  thf('58', plain,
% 0.90/1.12      (![X52 : $i, X53 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.90/1.12      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.90/1.12  thf('59', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.90/1.12      inference('sup-', [status(thm)], ['57', '58'])).
% 0.90/1.12  thf('60', plain,
% 0.90/1.12      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.90/1.12         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.90/1.12             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['55', '59'])).
% 0.90/1.12  thf('61', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.90/1.12      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.12  thf('62', plain,
% 0.90/1.12      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.90/1.12       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.90/1.12      inference('demod', [status(thm)], ['60', '61'])).
% 0.90/1.12  thf('63', plain,
% 0.90/1.12      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.90/1.12       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('64', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.90/1.12      inference('sat_resolution*', [status(thm)], ['5', '62', '63'])).
% 0.90/1.12  thf('65', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.90/1.12      inference('simpl_trail', [status(thm)], ['3', '64'])).
% 0.90/1.12  thf('66', plain,
% 0.90/1.12      (![X51 : $i]:
% 0.90/1.12         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 0.90/1.12      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.90/1.12  thf('67', plain,
% 0.90/1.12      (![X51 : $i]:
% 0.90/1.12         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 0.90/1.12      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.90/1.12  thf('68', plain,
% 0.90/1.12      (![X51 : $i]:
% 0.90/1.12         ((v3_ordinal1 @ (k1_ordinal1 @ X51)) | ~ (v3_ordinal1 @ X51))),
% 0.90/1.12      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.90/1.12  thf(connectedness_r1_ordinal1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.90/1.12       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.90/1.12  thf('69', plain,
% 0.90/1.12      (![X39 : $i, X40 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X39)
% 0.90/1.12          | ~ (v3_ordinal1 @ X40)
% 0.90/1.12          | (r1_ordinal1 @ X39 @ X40)
% 0.90/1.12          | (r1_ordinal1 @ X40 @ X39))),
% 0.90/1.12      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.90/1.12  thf('70', plain,
% 0.90/1.12      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('split', [status(esa)], ['4'])).
% 0.90/1.12  thf('71', plain,
% 0.90/1.12      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ~ (v3_ordinal1 @ sk_B)
% 0.90/1.12         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.12  thf('72', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('73', plain,
% 0.90/1.12      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['71', '72'])).
% 0.90/1.12  thf('74', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['68', '73'])).
% 0.90/1.12  thf('75', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('76', plain,
% 0.90/1.12      (((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['74', '75'])).
% 0.90/1.12  thf('77', plain,
% 0.90/1.12      (![X42 : $i, X43 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X42)
% 0.90/1.12          | ~ (v3_ordinal1 @ X43)
% 0.90/1.12          | (r1_tarski @ X42 @ X43)
% 0.90/1.12          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.90/1.12  thf('78', plain,
% 0.90/1.12      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ~ (v3_ordinal1 @ sk_B)))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['76', '77'])).
% 0.90/1.12  thf('79', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('80', plain,
% 0.90/1.12      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['78', '79'])).
% 0.90/1.12  thf('81', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['67', '80'])).
% 0.90/1.12  thf('82', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('83', plain,
% 0.90/1.12      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['81', '82'])).
% 0.90/1.12  thf('84', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X1)
% 0.90/1.12          | (r2_hidden @ X0 @ X1)
% 0.90/1.12          | ((X1) = (X0))
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | ~ (r1_tarski @ X0 @ X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.12  thf('85', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ sk_B)
% 0.90/1.12         | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.90/1.12         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['83', '84'])).
% 0.90/1.12  thf('86', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('87', plain,
% 0.90/1.12      (((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.90/1.12         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['85', '86'])).
% 0.90/1.12  thf('88', plain,
% 0.90/1.12      (((~ (v3_ordinal1 @ sk_A)
% 0.90/1.12         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ((k1_ordinal1 @ sk_A) = (sk_B))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['66', '87'])).
% 0.90/1.12  thf('89', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('90', plain,
% 0.90/1.12      ((((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.90/1.12         | ((k1_ordinal1 @ sk_A) = (sk_B))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['88', '89'])).
% 0.90/1.12  thf('91', plain,
% 0.90/1.12      (![X44 : $i, X45 : $i]:
% 0.90/1.12         (((X45) = (X44))
% 0.90/1.12          | (r2_hidden @ X45 @ X44)
% 0.90/1.12          | ~ (r2_hidden @ X45 @ (k1_ordinal1 @ X44)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.90/1.12  thf('92', plain,
% 0.90/1.12      (((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.90/1.12         | (r2_hidden @ sk_B @ sk_A)
% 0.90/1.12         | ((sk_B) = (sk_A))))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.12  thf('93', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.90/1.12      inference('sat_resolution*', [status(thm)], ['5', '62'])).
% 0.90/1.12  thf('94', plain,
% 0.90/1.12      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.90/1.12        | (r2_hidden @ sk_B @ sk_A)
% 0.90/1.12        | ((sk_B) = (sk_A)))),
% 0.90/1.12      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.90/1.12  thf('95', plain,
% 0.90/1.12      (![X52 : $i, X53 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.90/1.12      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.90/1.12  thf('96', plain,
% 0.90/1.12      ((((sk_B) = (sk_A))
% 0.90/1.12        | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.90/1.12        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.90/1.12      inference('sup-', [status(thm)], ['94', '95'])).
% 0.90/1.12  thf('97', plain,
% 0.90/1.12      (![X39 : $i, X40 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X39)
% 0.90/1.12          | ~ (v3_ordinal1 @ X40)
% 0.90/1.12          | (r1_ordinal1 @ X39 @ X40)
% 0.90/1.12          | (r1_ordinal1 @ X40 @ X39))),
% 0.90/1.12      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.90/1.12  thf('98', plain,
% 0.90/1.12      (![X42 : $i, X43 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X42)
% 0.90/1.12          | ~ (v3_ordinal1 @ X43)
% 0.90/1.12          | (r1_tarski @ X42 @ X43)
% 0.90/1.12          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.90/1.12  thf('99', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((r1_ordinal1 @ X0 @ X1)
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | ~ (v3_ordinal1 @ X1)
% 0.90/1.12          | (r1_tarski @ X1 @ X0)
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | ~ (v3_ordinal1 @ X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['97', '98'])).
% 0.90/1.12  thf('100', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((r1_tarski @ X1 @ X0)
% 0.90/1.12          | ~ (v3_ordinal1 @ X1)
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | (r1_ordinal1 @ X0 @ X1))),
% 0.90/1.12      inference('simplify', [status(thm)], ['99'])).
% 0.90/1.12  thf('101', plain,
% 0.90/1.12      (![X42 : $i, X43 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X42)
% 0.90/1.12          | ~ (v3_ordinal1 @ X43)
% 0.90/1.12          | (r1_tarski @ X42 @ X43)
% 0.90/1.12          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.90/1.12  thf('102', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X1)
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | (r1_tarski @ X0 @ X1)
% 0.90/1.12          | (r1_tarski @ X1 @ X0)
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | ~ (v3_ordinal1 @ X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['100', '101'])).
% 0.90/1.12  thf('103', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((r1_tarski @ X1 @ X0)
% 0.90/1.12          | (r1_tarski @ X0 @ X1)
% 0.90/1.12          | ~ (v3_ordinal1 @ X0)
% 0.90/1.12          | ~ (v3_ordinal1 @ X1))),
% 0.90/1.12      inference('simplify', [status(thm)], ['102'])).
% 0.90/1.12  thf('104', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.90/1.12      inference('simpl_trail', [status(thm)], ['3', '64'])).
% 0.90/1.12  thf('105', plain,
% 0.90/1.12      ((~ (v3_ordinal1 @ sk_B)
% 0.90/1.12        | ~ (v3_ordinal1 @ sk_A)
% 0.90/1.12        | (r1_tarski @ sk_A @ sk_B))),
% 0.90/1.12      inference('sup-', [status(thm)], ['103', '104'])).
% 0.90/1.12  thf('106', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('107', plain, ((v3_ordinal1 @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('108', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.90/1.12      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.90/1.12  thf('109', plain, ((((sk_B) = (sk_A)) | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['96', '108'])).
% 0.90/1.12  thf('110', plain,
% 0.90/1.12      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.90/1.12         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.90/1.12      inference('split', [status(esa)], ['4'])).
% 0.90/1.12  thf('111', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.90/1.12      inference('sat_resolution*', [status(thm)], ['5', '62'])).
% 0.90/1.12  thf('112', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.90/1.12      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.90/1.12  thf('113', plain, ((~ (r1_ordinal1 @ sk_B @ sk_B) | ((sk_B) = (sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['109', '112'])).
% 0.90/1.12  thf('114', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('115', plain,
% 0.90/1.12      (![X39 : $i, X40 : $i]:
% 0.90/1.12         (~ (v3_ordinal1 @ X39)
% 0.90/1.12          | ~ (v3_ordinal1 @ X40)
% 0.90/1.12          | (r1_ordinal1 @ X39 @ X40)
% 0.90/1.12          | (r1_ordinal1 @ X40 @ X39))),
% 0.90/1.12      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.90/1.12  thf('116', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         ((r1_ordinal1 @ X0 @ sk_B)
% 0.90/1.12          | (r1_ordinal1 @ sk_B @ X0)
% 0.90/1.12          | ~ (v3_ordinal1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['114', '115'])).
% 0.90/1.12  thf('117', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_B @ sk_B))),
% 0.90/1.12      inference('eq_fact', [status(thm)], ['116'])).
% 0.90/1.12  thf('118', plain, ((v3_ordinal1 @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('119', plain, ((r1_ordinal1 @ sk_B @ sk_B)),
% 0.90/1.12      inference('demod', [status(thm)], ['117', '118'])).
% 0.90/1.12  thf('120', plain, (((sk_B) = (sk_A))),
% 0.90/1.12      inference('demod', [status(thm)], ['113', '119'])).
% 0.90/1.12  thf('121', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.90/1.12      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.12  thf('122', plain, ($false),
% 0.90/1.12      inference('demod', [status(thm)], ['65', '120', '121'])).
% 0.90/1.12  
% 0.90/1.12  % SZS output end Refutation
% 0.90/1.12  
% 0.90/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
