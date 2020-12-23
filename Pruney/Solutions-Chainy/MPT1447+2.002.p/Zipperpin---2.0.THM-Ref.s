%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DbNetSfyG3

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 404 expanded)
%              Number of leaves         :   16 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          : 1467 (5339 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v15_lattices_type,type,(
    v15_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k7_filter_1_type,type,(
    k7_filter_1: $i > $i > $i )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(t42_filter_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v10_lattices @ B )
            & ( l3_lattices @ B ) )
         => ( ( ( v15_lattices @ A )
              & ( v15_lattices @ B ) )
          <=> ( v15_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v10_lattices @ B )
              & ( l3_lattices @ B ) )
           => ( ( ( v15_lattices @ A )
                & ( v15_lattices @ B ) )
            <=> ( v15_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_filter_1])).

thf('0',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v15_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v15_lattices @ sk_B )
    | ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v15_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k7_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) )
        & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( l3_lattices @ ( k7_filter_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf(d15_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v15_lattices @ A )
      <=> ( ( v13_lattices @ A )
          & ( v14_lattices @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v15_lattices @ X0 )
      | ( v14_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v14_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(fc2_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
        & ( v3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t41_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v10_lattices @ B )
            & ( l3_lattices @ B ) )
         => ( ( ( v14_lattices @ A )
              & ( v14_lattices @ B ) )
          <=> ( v14_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v14_lattices @ ( k7_filter_1 @ X8 @ X7 ) )
      | ( v14_lattices @ X7 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t41_filter_1])).

thf('22',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v14_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v14_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v14_lattices @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v14_lattices @ sk_B )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v13_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v15_lattices @ sk_B )
    | ~ ( v14_lattices @ sk_B )
    | ~ ( v13_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ~ ( v13_lattices @ sk_B )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( l3_lattices @ ( k7_filter_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v15_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(t40_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v10_lattices @ B )
            & ( l3_lattices @ B ) )
         => ( ( ( v13_lattices @ A )
              & ( v13_lattices @ B ) )
          <=> ( v13_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X6 @ X5 ) )
      | ( v13_lattices @ X5 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_filter_1])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v13_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v13_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v13_lattices @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v13_lattices @ sk_B )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( v15_lattices @ sk_B )
   <= ~ ( v15_lattices @ sk_B ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,
    ( ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v14_lattices @ ( k7_filter_1 @ X8 @ X7 ) )
      | ( v14_lattices @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t41_filter_1])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v14_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v14_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v14_lattices @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v14_lattices @ sk_A )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v13_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v15_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X6 @ X5 ) )
      | ( v13_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_filter_1])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v13_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v13_lattices @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v13_lattices @ sk_A )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v15_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v15_lattices @ sk_A )
   <= ~ ( v15_lattices @ sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('103',plain,
    ( ( v15_lattices @ sk_A )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('105',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v15_lattices @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('106',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v15_lattices @ X0 )
      | ( v14_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v14_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( v15_lattices @ sk_A )
    | ( v14_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v14_lattices @ sk_A )
   <= ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v15_lattices @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v15_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v13_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( v15_lattices @ sk_B )
    | ( v13_lattices @ sk_B ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v13_lattices @ sk_B )
   <= ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v13_lattices @ X6 )
      | ~ ( v13_lattices @ X5 )
      | ( v13_lattices @ ( k7_filter_1 @ X6 @ X5 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_filter_1])).

thf('120',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v14_lattices @ X8 )
      | ~ ( v14_lattices @ X7 )
      | ( v14_lattices @ ( k7_filter_1 @ X8 @ X7 ) )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t41_filter_1])).

thf('121',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( l3_lattices @ ( k7_filter_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v13_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v14_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v14_lattices @ X0 )
      | ~ ( v14_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v14_lattices @ X1 )
      | ~ ( v14_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v13_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v14_lattices @ X0 )
      | ~ ( v14_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v14_lattices @ X1 )
      | ~ ( v14_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v13_lattices @ X1 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v13_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ~ ( v14_lattices @ X1 )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v14_lattices @ X1 )
      | ~ ( v14_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v13_lattices @ X1 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['68'])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v13_lattices @ sk_B )
      | ~ ( v13_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v14_lattices @ sk_B )
      | ~ ( v14_lattices @ sk_A ) )
   <= ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_B )
      | ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v14_lattices @ sk_B )
      | ~ ( v14_lattices @ sk_A ) )
   <= ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133','134','135','136'])).

thf('138',plain,
    ( ( ~ ( v14_lattices @ sk_A )
      | ~ ( v14_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','137'])).

thf('139',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v15_lattices @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v15_lattices @ X0 )
      | ( v14_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v14_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ~ ( v15_lattices @ sk_B )
    | ( v14_lattices @ sk_B ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v14_lattices @ sk_B )
   <= ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,
    ( ( ~ ( v14_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','145'])).

thf('147',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_A )
      & ( v15_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','146'])).

thf('148',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v15_lattices @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('149',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v15_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d15_lattices])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ~ ( v15_lattices @ sk_A )
    | ( v13_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v13_lattices @ sk_A )
   <= ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_A )
      & ( v15_lattices @ sk_B ) ) ),
    inference(demod,[status(thm)],['147','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_A )
      & ( v15_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( v15_lattices @ sk_A )
    | ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('161',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','70','103','104','159','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DbNetSfyG3
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:52:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 64 iterations in 0.020s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.21/0.46  thf(v15_lattices_type, type, v15_lattices: $i > $o).
% 0.21/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.46  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.21/0.46  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.46  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.46  thf(k7_filter_1_type, type, k7_filter_1: $i > $i > $i).
% 0.21/0.46  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.21/0.46  thf(t42_filter_1, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.21/0.46             ( l3_lattices @ B ) ) =>
% 0.21/0.46           ( ( ( v15_lattices @ A ) & ( v15_lattices @ B ) ) <=>
% 0.21/0.46             ( v15_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.46            ( l3_lattices @ A ) ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.21/0.46                ( l3_lattices @ B ) ) =>
% 0.21/0.46              ( ( ( v15_lattices @ A ) & ( v15_lattices @ B ) ) <=>
% 0.21/0.46                ( v15_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t42_filter_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v15_lattices @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (((v15_lattices @ sk_B)) | ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v15_lattices @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('split', [status(esa)], ['2'])).
% 0.21/0.46  thf(dt_k7_filter_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.21/0.46         ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.21/0.46       ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.21/0.46         ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (l3_lattices @ X1)
% 0.21/0.46          | (v2_struct_0 @ X1)
% 0.21/0.46          | (v2_struct_0 @ X2)
% 0.21/0.46          | ~ (l3_lattices @ X2)
% 0.21/0.46          | (l3_lattices @ (k7_filter_1 @ X1 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k7_filter_1])).
% 0.21/0.46  thf(d15_lattices, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.46       ( ( v15_lattices @ A ) <=>
% 0.21/0.46         ( ( v13_lattices @ A ) & ( v14_lattices @ A ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v15_lattices @ X0)
% 0.21/0.46          | (v14_lattices @ X0)
% 0.21/0.46          | ~ (l3_lattices @ X0)
% 0.21/0.46          | (v2_struct_0 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (l3_lattices @ X0)
% 0.21/0.46          | (v2_struct_0 @ X0)
% 0.21/0.46          | (v2_struct_0 @ X1)
% 0.21/0.46          | ~ (l3_lattices @ X1)
% 0.21/0.46          | (v2_struct_0 @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.46          | (v14_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.46          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      ((((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | ~ (l3_lattices @ sk_A)
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | (v2_struct_0 @ sk_B)
% 0.21/0.46         | ~ (l3_lattices @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.46  thf('8', plain, ((l3_lattices @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain, ((l3_lattices @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | (v2_struct_0 @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.46  thf(fc2_filter_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.21/0.46         ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.21/0.46       ( ( ~( v2_struct_0 @ ( k7_filter_1 @ A @ B ) ) ) & 
% 0.21/0.46         ( v3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         (~ (l3_lattices @ X3)
% 0.21/0.46          | (v2_struct_0 @ X3)
% 0.21/0.46          | (v2_struct_0 @ X4)
% 0.21/0.46          | ~ (l3_lattices @ X4)
% 0.21/0.46          | ~ (v2_struct_0 @ (k7_filter_1 @ X3 @ X4)))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc2_filter_1])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((v2_struct_0 @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | (v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | ~ (l3_lattices @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | ~ (l3_lattices @ sk_A)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain, ((l3_lattices @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((((v2_struct_0 @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | (v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | (v2_struct_0 @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_A)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      ((((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | (v2_struct_0 @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.46  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      ((((v2_struct_0 @ sk_B) | (v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf(t41_filter_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.21/0.46             ( l3_lattices @ B ) ) =>
% 0.21/0.46           ( ( ( v14_lattices @ A ) & ( v14_lattices @ B ) ) <=>
% 0.21/0.46             ( v14_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i]:
% 0.21/0.46         ((v2_struct_0 @ X7)
% 0.21/0.46          | ~ (v10_lattices @ X7)
% 0.21/0.46          | ~ (l3_lattices @ X7)
% 0.21/0.46          | ~ (v14_lattices @ (k7_filter_1 @ X8 @ X7))
% 0.21/0.46          | (v14_lattices @ X7)
% 0.21/0.46          | ~ (l3_lattices @ X8)
% 0.21/0.46          | ~ (v10_lattices @ X8)
% 0.21/0.46          | (v2_struct_0 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [t41_filter_1])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      ((((v2_struct_0 @ sk_A)
% 0.21/0.46         | ~ (v10_lattices @ sk_A)
% 0.21/0.46         | ~ (l3_lattices @ sk_A)
% 0.21/0.46         | (v14_lattices @ sk_B)
% 0.21/0.46         | ~ (l3_lattices @ sk_B)
% 0.21/0.46         | ~ (v10_lattices @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf('23', plain, ((v10_lattices @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('24', plain, ((l3_lattices @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('25', plain, ((l3_lattices @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('26', plain, ((v10_lattices @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      ((((v2_struct_0 @ sk_A) | (v14_lattices @ sk_B) | (v2_struct_0 @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.21/0.46  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      ((((v2_struct_0 @ sk_B) | (v14_lattices @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.46  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('31', plain,
% 0.21/0.46      (((v14_lattices @ sk_B))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.46  thf('32', plain, ((l3_lattices @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('33', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v13_lattices @ X0)
% 0.21/0.46          | ~ (v14_lattices @ X0)
% 0.21/0.46          | (v15_lattices @ X0)
% 0.21/0.46          | ~ (l3_lattices @ X0)
% 0.21/0.46          | (v2_struct_0 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.46  thf('34', plain,
% 0.21/0.46      (((v2_struct_0 @ sk_B)
% 0.21/0.46        | (v15_lattices @ sk_B)
% 0.21/0.46        | ~ (v14_lattices @ sk_B)
% 0.21/0.46        | ~ (v13_lattices @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.46  thf('35', plain,
% 0.21/0.46      (((~ (v13_lattices @ sk_B) | (v15_lattices @ sk_B) | (v2_struct_0 @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['31', '34'])).
% 0.21/0.46  thf('36', plain,
% 0.21/0.46      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('split', [status(esa)], ['2'])).
% 0.21/0.46  thf('37', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (l3_lattices @ X1)
% 0.21/0.46          | (v2_struct_0 @ X1)
% 0.21/0.46          | (v2_struct_0 @ X2)
% 0.21/0.46          | ~ (l3_lattices @ X2)
% 0.21/0.46          | (l3_lattices @ (k7_filter_1 @ X1 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k7_filter_1])).
% 0.21/0.46  thf('38', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v15_lattices @ X0)
% 0.21/0.46          | (v13_lattices @ X0)
% 0.21/0.46          | ~ (l3_lattices @ X0)
% 0.21/0.46          | (v2_struct_0 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.46  thf('39', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (l3_lattices @ X0)
% 0.21/0.46          | (v2_struct_0 @ X0)
% 0.21/0.46          | (v2_struct_0 @ X1)
% 0.21/0.46          | ~ (l3_lattices @ X1)
% 0.21/0.46          | (v2_struct_0 @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.46          | (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.46          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.46  thf('40', plain,
% 0.21/0.46      ((((v13_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | ~ (l3_lattices @ sk_A)
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | (v2_struct_0 @ sk_B)
% 0.21/0.46         | ~ (l3_lattices @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.46  thf('41', plain, ((l3_lattices @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('42', plain, ((l3_lattices @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('43', plain,
% 0.21/0.46      ((((v13_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | (v2_struct_0 @ sk_B)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.46  thf('44', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         (~ (l3_lattices @ X3)
% 0.21/0.46          | (v2_struct_0 @ X3)
% 0.21/0.46          | (v2_struct_0 @ X4)
% 0.21/0.46          | ~ (l3_lattices @ X4)
% 0.21/0.46          | ~ (v2_struct_0 @ (k7_filter_1 @ X3 @ X4)))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc2_filter_1])).
% 0.21/0.46  thf('45', plain,
% 0.21/0.46      ((((v2_struct_0 @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | (v13_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.46         | ~ (l3_lattices @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_B)
% 0.21/0.46         | (v2_struct_0 @ sk_A)
% 0.21/0.46         | ~ (l3_lattices @ sk_A)))
% 0.21/0.46         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.46  thf('46', plain, ((l3_lattices @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('47', plain, ((l3_lattices @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('48', plain,
% 0.21/0.46      ((((v2_struct_0 @ sk_B)
% 0.21/0.47         | (v2_struct_0 @ sk_A)
% 0.21/0.47         | (v13_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.47         | (v2_struct_0 @ sk_B)
% 0.21/0.47         | (v2_struct_0 @ sk_A)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      ((((v13_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.47         | (v2_struct_0 @ sk_A)
% 0.21/0.47         | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.47  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('51', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_B) | (v13_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.47  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      (((v13_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.47  thf(t40_filter_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.21/0.47             ( l3_lattices @ B ) ) =>
% 0.21/0.47           ( ( ( v13_lattices @ A ) & ( v13_lattices @ B ) ) <=>
% 0.21/0.47             ( v13_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('54', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X5)
% 0.21/0.47          | ~ (v10_lattices @ X5)
% 0.21/0.47          | ~ (l3_lattices @ X5)
% 0.21/0.47          | ~ (v13_lattices @ (k7_filter_1 @ X6 @ X5))
% 0.21/0.47          | (v13_lattices @ X5)
% 0.21/0.47          | ~ (l3_lattices @ X6)
% 0.21/0.47          | ~ (v10_lattices @ X6)
% 0.21/0.47          | (v2_struct_0 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t40_filter_1])).
% 0.21/0.47  thf('55', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A)
% 0.21/0.47         | ~ (v10_lattices @ sk_A)
% 0.21/0.47         | ~ (l3_lattices @ sk_A)
% 0.21/0.47         | (v13_lattices @ sk_B)
% 0.21/0.47         | ~ (l3_lattices @ sk_B)
% 0.21/0.47         | ~ (v10_lattices @ sk_B)
% 0.21/0.47         | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.47  thf('56', plain, ((v10_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('57', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('58', plain, ((l3_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('59', plain, ((v10_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('60', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A) | (v13_lattices @ sk_B) | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.21/0.47  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('62', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_B) | (v13_lattices @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.47  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('64', plain,
% 0.21/0.47      (((v13_lattices @ sk_B))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.47  thf('65', plain,
% 0.21/0.47      ((((v15_lattices @ sk_B) | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['35', '64'])).
% 0.21/0.47  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('67', plain,
% 0.21/0.47      (((v15_lattices @ sk_B))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.47  thf('68', plain,
% 0.21/0.47      ((~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.21/0.47        | ~ (v15_lattices @ sk_B)
% 0.21/0.47        | ~ (v15_lattices @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('69', plain, ((~ (v15_lattices @ sk_B)) <= (~ ((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['68'])).
% 0.21/0.47  thf('70', plain,
% 0.21/0.47      (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | 
% 0.21/0.47       ((v15_lattices @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['67', '69'])).
% 0.21/0.47  thf('71', plain,
% 0.21/0.47      (((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('72', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X7)
% 0.21/0.47          | ~ (v10_lattices @ X7)
% 0.21/0.47          | ~ (l3_lattices @ X7)
% 0.21/0.47          | ~ (v14_lattices @ (k7_filter_1 @ X8 @ X7))
% 0.21/0.47          | (v14_lattices @ X8)
% 0.21/0.47          | ~ (l3_lattices @ X8)
% 0.21/0.47          | ~ (v10_lattices @ X8)
% 0.21/0.47          | (v2_struct_0 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t41_filter_1])).
% 0.21/0.47  thf('73', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A)
% 0.21/0.47         | ~ (v10_lattices @ sk_A)
% 0.21/0.47         | ~ (l3_lattices @ sk_A)
% 0.21/0.47         | (v14_lattices @ sk_A)
% 0.21/0.47         | ~ (l3_lattices @ sk_B)
% 0.21/0.47         | ~ (v10_lattices @ sk_B)
% 0.21/0.47         | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.47  thf('74', plain, ((v10_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('76', plain, ((l3_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('77', plain, ((v10_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('78', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A) | (v14_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.21/0.47  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('80', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_B) | (v14_lattices @ sk_A)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.47  thf('81', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('82', plain,
% 0.21/0.47      (((v14_lattices @ sk_A))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['80', '81'])).
% 0.21/0.47  thf('83', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('84', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v13_lattices @ X0)
% 0.21/0.47          | ~ (v14_lattices @ X0)
% 0.21/0.47          | (v15_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.47  thf('85', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | (v15_lattices @ sk_A)
% 0.21/0.47        | ~ (v14_lattices @ sk_A)
% 0.21/0.47        | ~ (v13_lattices @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.47  thf('86', plain,
% 0.21/0.47      (((~ (v13_lattices @ sk_A) | (v15_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['82', '85'])).
% 0.21/0.47  thf('87', plain,
% 0.21/0.47      (((v13_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.47  thf('88', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X5)
% 0.21/0.47          | ~ (v10_lattices @ X5)
% 0.21/0.47          | ~ (l3_lattices @ X5)
% 0.21/0.47          | ~ (v13_lattices @ (k7_filter_1 @ X6 @ X5))
% 0.21/0.47          | (v13_lattices @ X6)
% 0.21/0.47          | ~ (l3_lattices @ X6)
% 0.21/0.47          | ~ (v10_lattices @ X6)
% 0.21/0.47          | (v2_struct_0 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t40_filter_1])).
% 0.21/0.47  thf('89', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A)
% 0.21/0.47         | ~ (v10_lattices @ sk_A)
% 0.21/0.47         | ~ (l3_lattices @ sk_A)
% 0.21/0.47         | (v13_lattices @ sk_A)
% 0.21/0.47         | ~ (l3_lattices @ sk_B)
% 0.21/0.47         | ~ (v10_lattices @ sk_B)
% 0.21/0.47         | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.47  thf('90', plain, ((v10_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('91', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('92', plain, ((l3_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('93', plain, ((v10_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('94', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A) | (v13_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.21/0.47  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('96', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_B) | (v13_lattices @ sk_A)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['94', '95'])).
% 0.21/0.47  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('98', plain,
% 0.21/0.47      (((v13_lattices @ sk_A))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.47  thf('99', plain,
% 0.21/0.47      ((((v15_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['86', '98'])).
% 0.21/0.47  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('101', plain,
% 0.21/0.47      (((v15_lattices @ sk_A))
% 0.21/0.47         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['99', '100'])).
% 0.21/0.47  thf('102', plain, ((~ (v15_lattices @ sk_A)) <= (~ ((v15_lattices @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['68'])).
% 0.21/0.47  thf('103', plain,
% 0.21/0.47      (((v15_lattices @ sk_A)) | 
% 0.21/0.47       ~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.47  thf('104', plain,
% 0.21/0.47      (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | 
% 0.21/0.47       ~ ((v15_lattices @ sk_B)) | ~ ((v15_lattices @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['68'])).
% 0.21/0.47  thf('105', plain, (((v15_lattices @ sk_A)) <= (((v15_lattices @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('106', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('107', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v15_lattices @ X0)
% 0.21/0.47          | (v14_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.47  thf('108', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A) | (v14_lattices @ sk_A) | ~ (v15_lattices @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.47  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('110', plain, ((~ (v15_lattices @ sk_A) | (v14_lattices @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['108', '109'])).
% 0.21/0.47  thf('111', plain, (((v14_lattices @ sk_A)) <= (((v15_lattices @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['105', '110'])).
% 0.21/0.47  thf('112', plain, (((v15_lattices @ sk_B)) <= (((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('113', plain, ((l3_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('114', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v15_lattices @ X0)
% 0.21/0.47          | (v13_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.47  thf('115', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B) | (v13_lattices @ sk_B) | ~ (v15_lattices @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['113', '114'])).
% 0.21/0.47  thf('116', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('117', plain, ((~ (v15_lattices @ sk_B) | (v13_lattices @ sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['115', '116'])).
% 0.21/0.47  thf('118', plain, (((v13_lattices @ sk_B)) <= (((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['112', '117'])).
% 0.21/0.47  thf('119', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X5)
% 0.21/0.47          | ~ (v10_lattices @ X5)
% 0.21/0.47          | ~ (l3_lattices @ X5)
% 0.21/0.47          | ~ (v13_lattices @ X6)
% 0.21/0.47          | ~ (v13_lattices @ X5)
% 0.21/0.47          | (v13_lattices @ (k7_filter_1 @ X6 @ X5))
% 0.21/0.47          | ~ (l3_lattices @ X6)
% 0.21/0.47          | ~ (v10_lattices @ X6)
% 0.21/0.47          | (v2_struct_0 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t40_filter_1])).
% 0.21/0.47  thf('120', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X7)
% 0.21/0.47          | ~ (v10_lattices @ X7)
% 0.21/0.47          | ~ (l3_lattices @ X7)
% 0.21/0.47          | ~ (v14_lattices @ X8)
% 0.21/0.47          | ~ (v14_lattices @ X7)
% 0.21/0.47          | (v14_lattices @ (k7_filter_1 @ X8 @ X7))
% 0.21/0.47          | ~ (l3_lattices @ X8)
% 0.21/0.47          | ~ (v10_lattices @ X8)
% 0.21/0.47          | (v2_struct_0 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t41_filter_1])).
% 0.21/0.47  thf('121', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (l3_lattices @ X1)
% 0.21/0.47          | (v2_struct_0 @ X1)
% 0.21/0.47          | (v2_struct_0 @ X2)
% 0.21/0.47          | ~ (l3_lattices @ X2)
% 0.21/0.47          | (l3_lattices @ (k7_filter_1 @ X1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k7_filter_1])).
% 0.21/0.47  thf('122', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v13_lattices @ X0)
% 0.21/0.47          | ~ (v14_lattices @ X0)
% 0.21/0.47          | (v15_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.47  thf('123', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (l3_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | (v2_struct_0 @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | (v2_struct_0 @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v14_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v13_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.47  thf('124', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X1)
% 0.21/0.47          | ~ (v10_lattices @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | ~ (v14_lattices @ X0)
% 0.21/0.47          | ~ (v14_lattices @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | (v2_struct_0 @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | (v2_struct_0 @ X1)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['120', '123'])).
% 0.21/0.47  thf('125', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (v14_lattices @ X1)
% 0.21/0.47          | ~ (v14_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | ~ (v10_lattices @ X1)
% 0.21/0.47          | (v2_struct_0 @ X1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['124'])).
% 0.21/0.47  thf('126', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X1)
% 0.21/0.47          | ~ (v10_lattices @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | ~ (v13_lattices @ X0)
% 0.21/0.47          | ~ (v13_lattices @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | (v2_struct_0 @ X1)
% 0.21/0.47          | ~ (v10_lattices @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | ~ (v14_lattices @ X0)
% 0.21/0.47          | ~ (v14_lattices @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | (v2_struct_0 @ (k7_filter_1 @ X1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['119', '125'])).
% 0.21/0.47  thf('127', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v14_lattices @ X1)
% 0.21/0.47          | ~ (v14_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (v13_lattices @ X1)
% 0.21/0.47          | ~ (v13_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | ~ (v10_lattices @ X1)
% 0.21/0.47          | (v2_struct_0 @ X1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['126'])).
% 0.21/0.47  thf('128', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (l3_lattices @ X3)
% 0.21/0.47          | (v2_struct_0 @ X3)
% 0.21/0.47          | (v2_struct_0 @ X4)
% 0.21/0.47          | ~ (l3_lattices @ X4)
% 0.21/0.47          | ~ (v2_struct_0 @ (k7_filter_1 @ X3 @ X4)))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc2_filter_1])).
% 0.21/0.47  thf('129', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X1)
% 0.21/0.47          | ~ (v10_lattices @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | ~ (v13_lattices @ X0)
% 0.21/0.47          | ~ (v13_lattices @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v14_lattices @ X0)
% 0.21/0.47          | ~ (v14_lattices @ X1)
% 0.21/0.47          | (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | (v2_struct_0 @ X1)
% 0.21/0.47          | ~ (l3_lattices @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['127', '128'])).
% 0.21/0.47  thf('130', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v14_lattices @ X1)
% 0.21/0.47          | ~ (v14_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (v13_lattices @ X1)
% 0.21/0.47          | ~ (v13_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X1)
% 0.21/0.47          | ~ (v10_lattices @ X1)
% 0.21/0.47          | (v2_struct_0 @ X1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['129'])).
% 0.21/0.47  thf('131', plain,
% 0.21/0.47      ((~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.21/0.47         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['68'])).
% 0.21/0.47  thf('132', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A)
% 0.21/0.47         | ~ (v10_lattices @ sk_A)
% 0.21/0.47         | ~ (l3_lattices @ sk_A)
% 0.21/0.47         | ~ (v13_lattices @ sk_B)
% 0.21/0.47         | ~ (v13_lattices @ sk_A)
% 0.21/0.47         | ~ (l3_lattices @ sk_B)
% 0.21/0.47         | ~ (v10_lattices @ sk_B)
% 0.21/0.47         | (v2_struct_0 @ sk_B)
% 0.21/0.47         | ~ (v14_lattices @ sk_B)
% 0.21/0.47         | ~ (v14_lattices @ sk_A)))
% 0.21/0.47         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['130', '131'])).
% 0.21/0.47  thf('133', plain, ((v10_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('134', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('135', plain, ((l3_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('136', plain, ((v10_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('137', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A)
% 0.21/0.47         | ~ (v13_lattices @ sk_B)
% 0.21/0.47         | ~ (v13_lattices @ sk_A)
% 0.21/0.47         | (v2_struct_0 @ sk_B)
% 0.21/0.47         | ~ (v14_lattices @ sk_B)
% 0.21/0.47         | ~ (v14_lattices @ sk_A)))
% 0.21/0.47         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['132', '133', '134', '135', '136'])).
% 0.21/0.47  thf('138', plain,
% 0.21/0.47      (((~ (v14_lattices @ sk_A)
% 0.21/0.47         | ~ (v14_lattices @ sk_B)
% 0.21/0.47         | (v2_struct_0 @ sk_B)
% 0.21/0.47         | ~ (v13_lattices @ sk_A)
% 0.21/0.47         | (v2_struct_0 @ sk_A)))
% 0.21/0.47         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.21/0.47             ((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['118', '137'])).
% 0.21/0.47  thf('139', plain, (((v15_lattices @ sk_B)) <= (((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('140', plain, ((l3_lattices @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('141', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v15_lattices @ X0)
% 0.21/0.47          | (v14_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.47  thf('142', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B) | (v14_lattices @ sk_B) | ~ (v15_lattices @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['140', '141'])).
% 0.21/0.47  thf('143', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('144', plain, ((~ (v15_lattices @ sk_B) | (v14_lattices @ sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['142', '143'])).
% 0.21/0.47  thf('145', plain, (((v14_lattices @ sk_B)) <= (((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['139', '144'])).
% 0.21/0.47  thf('146', plain,
% 0.21/0.47      (((~ (v14_lattices @ sk_A)
% 0.21/0.47         | (v2_struct_0 @ sk_B)
% 0.21/0.47         | ~ (v13_lattices @ sk_A)
% 0.21/0.47         | (v2_struct_0 @ sk_A)))
% 0.21/0.47         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.21/0.47             ((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['138', '145'])).
% 0.21/0.47  thf('147', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A) | ~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.21/0.47             ((v15_lattices @ sk_A)) & 
% 0.21/0.47             ((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['111', '146'])).
% 0.21/0.47  thf('148', plain, (((v15_lattices @ sk_A)) <= (((v15_lattices @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('149', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('150', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v15_lattices @ X0)
% 0.21/0.47          | (v13_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d15_lattices])).
% 0.21/0.47  thf('151', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A) | (v13_lattices @ sk_A) | ~ (v15_lattices @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['149', '150'])).
% 0.21/0.47  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('153', plain, ((~ (v15_lattices @ sk_A) | (v13_lattices @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['151', '152'])).
% 0.21/0.47  thf('154', plain, (((v13_lattices @ sk_A)) <= (((v15_lattices @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['148', '153'])).
% 0.21/0.47  thf('155', plain,
% 0.21/0.47      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.21/0.47         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.21/0.47             ((v15_lattices @ sk_A)) & 
% 0.21/0.47             ((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['147', '154'])).
% 0.21/0.47  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('157', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B))
% 0.21/0.47         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.21/0.47             ((v15_lattices @ sk_A)) & 
% 0.21/0.47             ((v15_lattices @ sk_B)))),
% 0.21/0.47      inference('clc', [status(thm)], ['155', '156'])).
% 0.21/0.47  thf('158', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('159', plain,
% 0.21/0.47      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | 
% 0.21/0.47       ~ ((v15_lattices @ sk_A)) | ~ ((v15_lattices @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['157', '158'])).
% 0.21/0.47  thf('160', plain,
% 0.21/0.47      (((v15_lattices @ sk_A)) | ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('161', plain, ($false),
% 0.21/0.47      inference('sat_resolution*', [status(thm)],
% 0.21/0.47                ['1', '70', '103', '104', '159', '160'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
