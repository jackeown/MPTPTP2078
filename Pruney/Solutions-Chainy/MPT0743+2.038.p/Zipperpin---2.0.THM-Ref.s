%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CvgMyVSDJq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:58 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 387 expanded)
%              Number of leaves         :   15 ( 113 expanded)
%              Depth                    :   21
%              Number of atoms          :  653 (3188 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

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
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
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

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_ordinal1 @ X10 ) )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('46',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_ordinal1 @ X10 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
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
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( k1_ordinal1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('59',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','49'])).

thf('60',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('66',plain,
    ( ( sk_B = sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X3 @ X4 )
      | ( r1_ordinal1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','51'])).

thf('75',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['66','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['52','79','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CvgMyVSDJq
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 267 iterations in 0.133s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.41/0.59  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.41/0.59  thf(t33_ordinal1, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.59           ( ( r2_hidden @ A @ B ) <=>
% 0.41/0.59             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( v3_ordinal1 @ A ) =>
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ( v3_ordinal1 @ B ) =>
% 0.41/0.59              ( ( r2_hidden @ A @ B ) <=>
% 0.41/0.59                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf(t7_ordinal1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.59        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.41/0.59       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.59      inference('split', [status(esa)], ['4'])).
% 0.41/0.59  thf(t29_ordinal1, axiom,
% 0.41/0.59    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X14 : $i]:
% 0.41/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf(redefinition_r1_ordinal1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.41/0.59       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X6)
% 0.41/0.59          | ~ (v3_ordinal1 @ X7)
% 0.41/0.59          | (r1_tarski @ X6 @ X7)
% 0.41/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '11'])).
% 0.41/0.59  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf(t26_ordinal1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.59           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X12)
% 0.41/0.59          | (r1_ordinal1 @ X13 @ X12)
% 0.41/0.59          | (r2_hidden @ X12 @ X13)
% 0.41/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.41/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.59  thf(t13_ordinal1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.41/0.59       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i]:
% 0.41/0.59         ((r2_hidden @ X9 @ (k1_ordinal1 @ X10)) | ~ (r2_hidden @ X9 @ X10))),
% 0.41/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X0)
% 0.41/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1)
% 0.41/0.59          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X1)
% 0.41/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X0)
% 0.41/0.59          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (((~ (v3_ordinal1 @ sk_A)
% 0.41/0.59         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_B)))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['14', '19'])).
% 0.41/0.59  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (((r1_ordinal1 @ sk_A @ sk_B))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X6)
% 0.41/0.59          | ~ (v3_ordinal1 @ X7)
% 0.41/0.59          | (r1_tarski @ X6 @ X7)
% 0.41/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      ((((r1_tarski @ sk_A @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_A)))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.59  thf('26', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (((r1_tarski @ sk_A @ sk_B))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X12)
% 0.41/0.59          | (r1_ordinal1 @ X13 @ X12)
% 0.41/0.59          | (r2_hidden @ X12 @ X13)
% 0.41/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.41/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['4'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (((~ (v3_ordinal1 @ sk_B)
% 0.41/0.59         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.59  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X6)
% 0.41/0.59          | ~ (v3_ordinal1 @ X7)
% 0.41/0.59          | (r1_tarski @ X6 @ X7)
% 0.41/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      ((((r1_tarski @ sk_B @ sk_A)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_A)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.59  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.41/0.59  thf(d10_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (![X0 : $i, X2 : $i]:
% 0.41/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      (((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.41/0.59         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      ((((sk_A) = (sk_B)))
% 0.41/0.59         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.41/0.59             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['28', '41'])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.41/0.59         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.41/0.59             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i]:
% 0.41/0.59         ((r2_hidden @ X9 @ (k1_ordinal1 @ X10)) | ((X9) != (X10)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.41/0.59  thf('46', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_ordinal1 @ X10))),
% 0.41/0.59      inference('simplify', [status(thm)], ['45'])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.59  thf('48', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.41/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.41/0.59       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['44', '48'])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.41/0.59       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('51', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 0.41/0.59  thf('52', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['3', '51'])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (![X14 : $i]:
% 0.41/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X12)
% 0.41/0.59          | (r1_ordinal1 @ X13 @ X12)
% 0.41/0.59          | (r2_hidden @ X12 @ X13)
% 0.41/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.41/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i]:
% 0.41/0.59         (((X9) = (X8))
% 0.41/0.59          | (r2_hidden @ X9 @ X8)
% 0.41/0.59          | ~ (r2_hidden @ X9 @ (k1_ordinal1 @ X8)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.41/0.59  thf('56', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.41/0.59          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1)
% 0.41/0.59          | (r2_hidden @ X1 @ X0)
% 0.41/0.59          | ((X1) = (X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X0)
% 0.41/0.59          | ((X1) = (X0))
% 0.41/0.59          | (r2_hidden @ X1 @ X0)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1)
% 0.41/0.59          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['53', '56'])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.59         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['4'])).
% 0.41/0.59  thf('59', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['5', '49'])).
% 0.41/0.59  thf('60', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      ((~ (v3_ordinal1 @ sk_B)
% 0.41/0.59        | (r2_hidden @ sk_B @ sk_A)
% 0.41/0.59        | ((sk_B) = (sk_A))
% 0.41/0.59        | ~ (v3_ordinal1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['57', '60'])).
% 0.41/0.59  thf('62', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('63', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('64', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.41/0.59  thf('65', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.59  thf('66', plain, ((((sk_B) = (sk_A)) | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.41/0.59  thf(connectedness_r1_ordinal1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.41/0.59       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.41/0.59  thf('67', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X3)
% 0.41/0.59          | ~ (v3_ordinal1 @ X4)
% 0.41/0.59          | (r1_ordinal1 @ X3 @ X4)
% 0.41/0.59          | (r1_ordinal1 @ X4 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.41/0.59  thf('68', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X6)
% 0.41/0.59          | ~ (v3_ordinal1 @ X7)
% 0.41/0.59          | (r1_tarski @ X6 @ X7)
% 0.41/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.59  thf('69', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r1_ordinal1 @ X0 @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X0)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1)
% 0.41/0.59          | (r1_tarski @ X1 @ X0)
% 0.41/0.59          | ~ (v3_ordinal1 @ X0)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.41/0.59  thf('70', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r1_tarski @ X1 @ X0)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X0)
% 0.41/0.59          | (r1_ordinal1 @ X0 @ X1))),
% 0.41/0.59      inference('simplify', [status(thm)], ['69'])).
% 0.41/0.59  thf('71', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X6)
% 0.41/0.59          | ~ (v3_ordinal1 @ X7)
% 0.41/0.59          | (r1_tarski @ X6 @ X7)
% 0.41/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.59  thf('72', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X0)
% 0.41/0.59          | (r1_tarski @ X0 @ X1)
% 0.41/0.59          | (r1_tarski @ X1 @ X0)
% 0.41/0.59          | ~ (v3_ordinal1 @ X0)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r1_tarski @ X1 @ X0)
% 0.41/0.59          | (r1_tarski @ X0 @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X0)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.41/0.59      inference('simplify', [status(thm)], ['72'])).
% 0.41/0.59  thf('74', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['3', '51'])).
% 0.41/0.59  thf('75', plain,
% 0.41/0.59      ((~ (v3_ordinal1 @ sk_B)
% 0.41/0.59        | ~ (v3_ordinal1 @ sk_A)
% 0.41/0.59        | (r1_tarski @ sk_A @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['73', '74'])).
% 0.41/0.59  thf('76', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('77', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('78', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.41/0.59      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.41/0.59  thf('79', plain, (((sk_B) = (sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['66', '78'])).
% 0.41/0.59  thf('80', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('81', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.59      inference('simplify', [status(thm)], ['80'])).
% 0.41/0.59  thf('82', plain, ($false),
% 0.41/0.59      inference('demod', [status(thm)], ['52', '79', '81'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
