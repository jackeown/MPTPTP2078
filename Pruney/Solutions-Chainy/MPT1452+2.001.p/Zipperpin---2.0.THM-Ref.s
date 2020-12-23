%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D3kpOdtsEV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:22 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  344 (14201 expanded)
%              Number of leaves         :   17 (3585 expanded)
%              Depth                    :   30
%              Number of atoms          : 3451 (337841 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k7_filter_1_type,type,(
    k7_filter_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(v16_lattices_type,type,(
    v16_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v15_lattices_type,type,(
    v15_lattices: $i > $o )).

thf(t47_filter_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v10_lattices @ B )
            & ( l3_lattices @ B ) )
         => ( ( ~ ( v2_struct_0 @ A )
              & ( v10_lattices @ A )
              & ( v17_lattices @ A )
              & ( l3_lattices @ A )
              & ~ ( v2_struct_0 @ B )
              & ( v10_lattices @ B )
              & ( v17_lattices @ B )
              & ( l3_lattices @ B ) )
          <=> ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
              & ( v10_lattices @ ( k7_filter_1 @ A @ B ) )
              & ( v17_lattices @ ( k7_filter_1 @ A @ B ) )
              & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v10_lattices @ B )
              & ( l3_lattices @ B ) )
           => ( ( ~ ( v2_struct_0 @ A )
                & ( v10_lattices @ A )
                & ( v17_lattices @ A )
                & ( l3_lattices @ A )
                & ~ ( v2_struct_0 @ B )
                & ( v10_lattices @ B )
                & ( v17_lattices @ B )
                & ( l3_lattices @ B ) )
            <=> ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
                & ( v10_lattices @ ( k7_filter_1 @ A @ B ) )
                & ( v17_lattices @ ( k7_filter_1 @ A @ B ) )
                & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_filter_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf(cc5_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('4',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(dt_k7_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) )
        & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( l3_lattices @ ( k7_filter_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('10',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['19'])).

thf('21',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('22',plain,
    ( ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','21'])).

thf('23',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('24',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v17_lattices @ sk_A )
    | ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v17_lattices @ sk_B )
    | ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v11_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v11_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v11_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v17_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v11_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v11_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v11_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t39_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v10_lattices @ B )
            & ( l3_lattices @ B ) )
         => ( ( ~ ( v2_struct_0 @ A )
              & ( v10_lattices @ A )
              & ( v11_lattices @ A )
              & ( l3_lattices @ A )
              & ~ ( v2_struct_0 @ B )
              & ( v10_lattices @ B )
              & ( v11_lattices @ B )
              & ( l3_lattices @ B ) )
          <=> ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
              & ( v10_lattices @ ( k7_filter_1 @ A @ B ) )
              & ( v11_lattices @ ( k7_filter_1 @ A @ B ) )
              & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v2_struct_0 @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_B ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_B ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( ~ ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v11_lattices @ sk_B ) )
   <= ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( v11_lattices @ sk_B )
   <= ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['34','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['25','27','56'])).

thf('58',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['23','57'])).

thf('59',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['23','57'])).

thf('64',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf(t46_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v10_lattices @ B )
            & ( l3_lattices @ B ) )
         => ( ( ~ ( v2_struct_0 @ A )
              & ( v10_lattices @ A )
              & ( v15_lattices @ A )
              & ( v16_lattices @ A )
              & ( l3_lattices @ A )
              & ~ ( v2_struct_0 @ B )
              & ( v10_lattices @ B )
              & ( v15_lattices @ B )
              & ( v16_lattices @ B )
              & ( l3_lattices @ B ) )
          <=> ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
              & ( v10_lattices @ ( k7_filter_1 @ A @ B ) )
              & ( v15_lattices @ ( k7_filter_1 @ A @ B ) )
              & ( v16_lattices @ ( k7_filter_1 @ A @ B ) )
              & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ( v16_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v16_lattices @ sk_A )
      | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('71',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v16_lattices @ sk_A )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v16_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('77',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('78',plain,
    ( ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('80',plain,
    ( ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['25','27','56'])).

thf('83',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v16_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','83'])).

thf('85',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['25','27','56'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v16_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v16_lattices @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v16_lattices @ sk_A )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf(cc6_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) ) ) ) )).

thf('93',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ( v17_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc6_lattices])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v17_lattices @ sk_A )
    | ~ ( v16_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v17_lattices @ sk_A )
    | ~ ( v16_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ~ ( v11_lattices @ sk_A )
      | ~ ( v15_lattices @ sk_A )
      | ( v17_lattices @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('101',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('102',plain,
    ( ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('104',plain,
    ( ( ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['25','27','56'])).

thf('107',plain,
    ( ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('109',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ( v11_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v11_lattices @ sk_A )
      | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('114',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v11_lattices @ sk_A )
      | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v11_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v11_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v11_lattices @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v11_lattices @ sk_A )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('125',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('126',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ( v15_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v15_lattices @ sk_A )
      | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('131',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v15_lattices @ sk_A )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['23','57'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('138',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v15_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v15_lattices @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v15_lattices @ sk_A )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v17_lattices @ sk_A )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['98','123','142'])).

thf('144',plain,
    ( ~ ( v17_lattices @ sk_A )
   <= ~ ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('145',plain,
    ( ( v17_lattices @ sk_A )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( v11_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('147',plain,
    ( ( v17_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('148',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ( v10_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('149',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v10_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('151',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('153',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v17_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','153','154','155','156'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','157'])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v17_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','158'])).

thf('160',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v17_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160','161','162','163'])).

thf('165',plain,
    ( ( ~ ( v17_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v11_lattices @ sk_B )
      | ~ ( v11_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ sk_B ) )
   <= ( ( v17_lattices @ sk_A )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['147','165'])).

thf('167',plain,
    ( ( v11_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ sk_B ) )
   <= ( ( v17_lattices @ sk_A )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v17_lattices @ sk_A )
      & ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['146','168'])).

thf('170',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('171',plain,
    ( ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v17_lattices @ sk_A )
      & ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v17_lattices @ sk_A )
      & ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( v17_lattices @ sk_A )
      & ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ~ ( v17_lattices @ sk_B )
    | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v16_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v16_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( v16_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['178','183'])).

thf('185',plain,
    ( ( v11_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('186',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ( v11_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('187',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v11_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( v15_lattices @ X7 )
      | ~ ( v16_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( v15_lattices @ X6 )
      | ~ ( v16_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v15_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('189',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v15_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v16_lattices @ X6 )
      | ~ ( v15_lattices @ X6 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v16_lattices @ X7 )
      | ~ ( v15_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( v15_lattices @ X7 )
      | ~ ( v16_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( v15_lattices @ X6 )
      | ~ ( v16_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v16_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('191',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v16_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v16_lattices @ X6 )
      | ~ ( v15_lattices @ X6 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v16_lattices @ X7 )
      | ~ ( v15_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( l3_lattices @ ( k7_filter_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('193',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ( v17_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc6_lattices])).

thf('194',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( v15_lattices @ X7 )
      | ~ ( v16_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( v15_lattices @ X6 )
      | ~ ( v16_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('195',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_struct_0 @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v16_lattices @ X6 )
      | ~ ( v15_lattices @ X6 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v16_lattices @ X7 )
      | ~ ( v15_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( v16_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['193','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v16_lattices @ X0 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['192','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v16_lattices @ X0 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['191','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ X0 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( v16_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( v16_lattices @ X0 )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ X0 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v11_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( v16_lattices @ X0 )
      | ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['187','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ X0 )
      | ~ ( v15_lattices @ X0 )
      | ~ ( v16_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('206',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_B )
      | ~ ( v15_lattices @ sk_A )
      | ~ ( v16_lattices @ sk_A )
      | ~ ( v15_lattices @ sk_B )
      | ~ ( v16_lattices @ sk_B ) )
   <= ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_B )
      | ~ ( v15_lattices @ sk_A )
      | ~ ( v16_lattices @ sk_A )
      | ~ ( v15_lattices @ sk_B )
      | ~ ( v16_lattices @ sk_B ) )
   <= ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['206','207','208','209','210'])).

thf('212',plain,
    ( ( ~ ( v16_lattices @ sk_B )
      | ~ ( v15_lattices @ sk_B )
      | ~ ( v16_lattices @ sk_A )
      | ~ ( v15_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['185','211'])).

thf('213',plain,
    ( ( v17_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('215',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v16_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( v16_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( v16_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['213','218'])).

thf('220',plain,
    ( ( v17_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v15_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['220','225'])).

thf('227',plain,
    ( ( ~ ( v16_lattices @ sk_B )
      | ~ ( v15_lattices @ sk_B )
      | ~ ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['212','219','226'])).

thf('228',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v11_lattices @ sk_B )
      | ~ ( v15_lattices @ sk_B ) )
   <= ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ sk_A )
      & ( v17_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['184','227'])).

thf('229',plain,
    ( ( v11_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('230',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v15_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( v15_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['230','235'])).

thf('237',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ sk_A )
      & ( v17_lattices @ sk_B ) ) ),
    inference(demod,[status(thm)],['228','229','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ sk_A )
      & ( v17_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['242'])).

thf('244',plain,(
    v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','62','145','177','241','243'])).

thf('245',plain,(
    v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['58','244'])).

thf('246',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v10_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('247',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ( v16_lattices @ X6 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v11_lattices @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v16_lattices @ X0 )
      | ~ ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_B )
    | ( v16_lattices @ sk_B )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['245','249'])).

thf('251',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( v11_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('255',plain,(
    v17_lattices @ sk_A ),
    inference('sat_resolution*',[status(thm)],['60','62','145'])).

thf('256',plain,(
    v11_lattices @ sk_A ),
    inference(simpl_trail,[status(thm)],['254','255'])).

thf('257',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('259',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('260',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X5 @ X4 ) )
      | ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('261',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v11_lattices @ sk_B )
      | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('265',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v11_lattices @ sk_B )
      | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['261','262','263','264','265','266'])).

thf('268',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['258','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('270',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v11_lattices @ sk_B ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v11_lattices @ sk_B )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['272','273'])).

thf('275',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['275'])).

thf('277',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','62','145','177','241','276'])).

thf('278',plain,(
    v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','62','145','177','241','243'])).

thf('279',plain,(
    v11_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['274','277','278'])).

thf('280',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('281',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v16_lattices @ sk_B )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['250','251','252','253','256','257','279','280'])).

thf('282',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('283',plain,(
    v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','62','145','177','241','243'])).

thf('284',plain,(
    v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v16_lattices @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['281','284'])).

thf('286',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('287',plain,
    ( ( v16_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ( v17_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc6_lattices])).

thf('289',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v17_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v11_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( v17_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v11_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['290','291'])).

thf('293',plain,(
    v11_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['274','277','278'])).

thf('294',plain,
    ( ( v17_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['292','293'])).

thf('295',plain,
    ( ~ ( v17_lattices @ sk_B )
   <= ~ ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('296',plain,(
    ~ ( v17_lattices @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','62','145','177','241'])).

thf('297',plain,(
    ~ ( v17_lattices @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['295','296'])).

thf('298',plain,
    ( ~ ( v15_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B ) ),
    inference(clc,[status(thm)],['294','297'])).

thf('299',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('300',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('301',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ( v15_lattices @ X6 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('302',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v15_lattices @ sk_B )
      | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','20'])).

thf('306',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v15_lattices @ sk_B )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['302','303','304','305','306','307'])).

thf('309',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['299','308'])).

thf('310',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['23','57'])).

thf('311',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['309','310'])).

thf('312',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','62','145','177','241','276'])).

thf('313',plain,(
    v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','62','145','177','241','243'])).

thf('314',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v15_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['311','312','313'])).

thf('315',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('316',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v15_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v15_lattices @ sk_B ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('319',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    v15_lattices @ sk_B ),
    inference(clc,[status(thm)],['318','319'])).

thf('321',plain,(
    ~ ( v16_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['298','320'])).

thf('322',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['287','321'])).

thf('323',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['322','323'])).

thf('325',plain,(
    $false ),
    inference(demod,[status(thm)],['0','324'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D3kpOdtsEV
% 0.10/0.31  % Computer   : n010.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 20:49:14 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running portfolio for 600 s
% 0.10/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.31  % Number of cores: 8
% 0.17/0.32  % Python version: Python 3.6.8
% 0.17/0.32  % Running in FO mode
% 0.17/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.17/0.52  % Solved by: fo/fo7.sh
% 0.17/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.52  % done 363 iterations in 0.098s
% 0.17/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.17/0.52  % SZS output start Refutation
% 0.17/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.52  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 0.17/0.52  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 0.17/0.52  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.17/0.52  thf(k7_filter_1_type, type, k7_filter_1: $i > $i > $i).
% 0.17/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.17/0.52  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.17/0.52  thf(v16_lattices_type, type, v16_lattices: $i > $o).
% 0.17/0.52  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.17/0.52  thf(v15_lattices_type, type, v15_lattices: $i > $o).
% 0.17/0.52  thf(t47_filter_1, conjecture,
% 0.17/0.52    (![A:$i]:
% 0.17/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.17/0.52       ( ![B:$i]:
% 0.17/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.17/0.52             ( l3_lattices @ B ) ) =>
% 0.17/0.52           ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.17/0.52               ( v17_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.17/0.52               ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.17/0.52               ( v17_lattices @ B ) & ( l3_lattices @ B ) ) <=>
% 0.17/0.52             ( ( ~( v2_struct_0 @ ( k7_filter_1 @ A @ B ) ) ) & 
% 0.17/0.52               ( v10_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.52               ( v17_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.52               ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) ))).
% 0.17/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.52    (~( ![A:$i]:
% 0.17/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.17/0.52            ( l3_lattices @ A ) ) =>
% 0.17/0.52          ( ![B:$i]:
% 0.17/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.17/0.52                ( l3_lattices @ B ) ) =>
% 0.17/0.52              ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.17/0.52                  ( v17_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.17/0.52                  ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.17/0.52                  ( v17_lattices @ B ) & ( l3_lattices @ B ) ) <=>
% 0.17/0.52                ( ( ~( v2_struct_0 @ ( k7_filter_1 @ A @ B ) ) ) & 
% 0.17/0.52                  ( v10_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.52                  ( v17_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.52                  ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.17/0.52    inference('cnf.neg', [status(esa)], [t47_filter_1])).
% 0.17/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('1', plain,
% 0.17/0.52      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | ~ (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('2', plain,
% 0.17/0.52      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.52         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.52      inference('split', [status(esa)], ['1'])).
% 0.17/0.52  thf(cc5_lattices, axiom,
% 0.17/0.52    (![A:$i]:
% 0.17/0.52     ( ( l3_lattices @ A ) =>
% 0.17/0.52       ( ( ( ~( v2_struct_0 @ A ) ) & ( v17_lattices @ A ) ) =>
% 0.17/0.52         ( ( ~( v2_struct_0 @ A ) ) & ( v11_lattices @ A ) & 
% 0.17/0.52           ( v15_lattices @ A ) & ( v16_lattices @ A ) ) ) ))).
% 0.17/0.52  thf('3', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         ((v2_struct_0 @ X0)
% 0.17/0.52          | ~ (v17_lattices @ X0)
% 0.17/0.52          | (v15_lattices @ X0)
% 0.17/0.52          | ~ (l3_lattices @ X0))),
% 0.17/0.52      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.52  thf('4', plain,
% 0.17/0.52      ((~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)) | ~ (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('5', plain,
% 0.17/0.52      ((~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.52         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.52      inference('split', [status(esa)], ['4'])).
% 0.17/0.52  thf('6', plain,
% 0.17/0.52      (((~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.52         | (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.52         | ~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.17/0.52         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.52      inference('sup-', [status(thm)], ['3', '5'])).
% 0.17/0.52  thf('7', plain,
% 0.17/0.52      (((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v17_lattices @ sk_A))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('8', plain,
% 0.17/0.52      (((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['7'])).
% 0.17/0.53  thf(dt_k7_filter_1, axiom,
% 0.17/0.53    (![A:$i,B:$i]:
% 0.17/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.17/0.53         ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.17/0.53       ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.53         ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ))).
% 0.17/0.53  thf('9', plain,
% 0.17/0.53      (![X2 : $i, X3 : $i]:
% 0.17/0.53         (~ (l3_lattices @ X2)
% 0.17/0.53          | (v2_struct_0 @ X2)
% 0.17/0.53          | (v2_struct_0 @ X3)
% 0.17/0.53          | ~ (l3_lattices @ X3)
% 0.17/0.53          | (l3_lattices @ (k7_filter_1 @ X2 @ X3)))),
% 0.17/0.53      inference('cnf', [status(esa)], [dt_k7_filter_1])).
% 0.17/0.53  thf('10', plain,
% 0.17/0.53      ((~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (l3_lattices @ sk_B)
% 0.17/0.53        | ~ (v17_lattices @ sk_B)
% 0.17/0.53        | ~ (v10_lattices @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ sk_B)
% 0.17/0.53        | ~ (l3_lattices @ sk_A)
% 0.17/0.53        | ~ (v17_lattices @ sk_A)
% 0.17/0.53        | ~ (v10_lattices @ sk_A)
% 0.17/0.53        | (v2_struct_0 @ sk_A))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('11', plain,
% 0.17/0.53      ((~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (~ ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['10'])).
% 0.17/0.53  thf('12', plain,
% 0.17/0.53      (((~ (l3_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)))
% 0.17/0.53         <= (~ ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['9', '11'])).
% 0.17/0.53  thf('13', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('15', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (~ ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.17/0.53  thf('16', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('17', plain,
% 0.17/0.53      (((v2_struct_0 @ sk_A))
% 0.17/0.53         <= (~ ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.17/0.53  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('19', plain, (((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.17/0.53  thf('20', plain, (((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)], ['19'])).
% 0.17/0.53  thf('21', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('22', plain,
% 0.17/0.53      ((((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['6', '21'])).
% 0.17/0.53  thf('23', plain,
% 0.17/0.53      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['2', '22'])).
% 0.17/0.53  thf('24', plain,
% 0.17/0.53      ((~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)) | (v17_lattices @ sk_A))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('25', plain,
% 0.17/0.53      (((v17_lattices @ sk_A)) | 
% 0.17/0.53       ~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('split', [status(esa)], ['24'])).
% 0.17/0.53  thf('26', plain,
% 0.17/0.53      ((~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)) | (v17_lattices @ sk_B))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('27', plain,
% 0.17/0.53      (((v17_lattices @ sk_B)) | 
% 0.17/0.53       ~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('split', [status(esa)], ['26'])).
% 0.17/0.53  thf('28', plain, (((v17_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('split', [status(esa)], ['26'])).
% 0.17/0.53  thf('29', plain,
% 0.17/0.53      (![X0 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v17_lattices @ X0)
% 0.17/0.53          | (v11_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.53  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('31', plain,
% 0.17/0.53      ((~ (l3_lattices @ sk_B)
% 0.17/0.53        | (v11_lattices @ sk_B)
% 0.17/0.53        | ~ (v17_lattices @ sk_B))),
% 0.17/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.17/0.53  thf('32', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('33', plain, (((v11_lattices @ sk_B) | ~ (v17_lattices @ sk_B))),
% 0.17/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.17/0.53  thf('34', plain, (((v11_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['28', '33'])).
% 0.17/0.53  thf('35', plain, (((v17_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('split', [status(esa)], ['24'])).
% 0.17/0.53  thf('36', plain,
% 0.17/0.53      (![X0 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v17_lattices @ X0)
% 0.17/0.53          | (v11_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.53  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('38', plain,
% 0.17/0.53      ((~ (l3_lattices @ sk_A)
% 0.17/0.53        | (v11_lattices @ sk_A)
% 0.17/0.53        | ~ (v17_lattices @ sk_A))),
% 0.17/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.17/0.53  thf('39', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('40', plain, (((v11_lattices @ sk_A) | ~ (v17_lattices @ sk_A))),
% 0.17/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.17/0.53  thf('41', plain, (((v11_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['35', '40'])).
% 0.17/0.53  thf('42', plain,
% 0.17/0.53      (((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['10'])).
% 0.17/0.53  thf(t39_filter_1, axiom,
% 0.17/0.53    (![A:$i]:
% 0.17/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.17/0.53       ( ![B:$i]:
% 0.17/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.17/0.53             ( l3_lattices @ B ) ) =>
% 0.17/0.53           ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.17/0.53               ( v11_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.17/0.53               ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.17/0.53               ( v11_lattices @ B ) & ( l3_lattices @ B ) ) <=>
% 0.17/0.53             ( ( ~( v2_struct_0 @ ( k7_filter_1 @ A @ B ) ) ) & 
% 0.17/0.53               ( v10_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.53               ( v11_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.53               ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) ))).
% 0.17/0.53  thf('43', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | ~ (v11_lattices @ X5)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | ~ (v11_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | ~ (v2_struct_0 @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5))),
% 0.17/0.53      inference('cnf', [status(esa)], [t39_filter_1])).
% 0.17/0.53  thf('44', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         (~ (v2_struct_0 @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (v11_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v11_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ X4))),
% 0.17/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.17/0.53  thf('45', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | ~ (v10_lattices @ sk_B)
% 0.17/0.53         | ~ (l3_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v10_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)))
% 0.17/0.53         <= (((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['42', '44'])).
% 0.17/0.53  thf('46', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('47', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('48', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('49', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('50', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)))
% 0.17/0.53         <= (((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.17/0.53  thf('51', plain,
% 0.17/0.53      (((~ (v11_lattices @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['41', '50'])).
% 0.17/0.53  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('53', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B) | ~ (v11_lattices @ sk_B)))
% 0.17/0.53         <= (((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('clc', [status(thm)], ['51', '52'])).
% 0.17/0.53  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('55', plain,
% 0.17/0.53      ((~ (v11_lattices @ sk_B))
% 0.17/0.53         <= (((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('clc', [status(thm)], ['53', '54'])).
% 0.17/0.53  thf('56', plain,
% 0.17/0.53      (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))) | 
% 0.17/0.53       ~ ((v17_lattices @ sk_A)) | ~ ((v17_lattices @ sk_B))),
% 0.17/0.53      inference('sup-', [status(thm)], ['34', '55'])).
% 0.17/0.53  thf('57', plain, (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)], ['25', '27', '56'])).
% 0.17/0.53  thf('58', plain,
% 0.17/0.53      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['23', '57'])).
% 0.17/0.53  thf('59', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v17_lattices @ sk_A))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('60', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | ((v17_lattices @ sk_A))),
% 0.17/0.53      inference('split', [status(esa)], ['59'])).
% 0.17/0.53  thf('61', plain,
% 0.17/0.53      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v17_lattices @ sk_A))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('62', plain,
% 0.17/0.53      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | ((v17_lattices @ sk_A))),
% 0.17/0.53      inference('split', [status(esa)], ['61'])).
% 0.17/0.53  thf('63', plain,
% 0.17/0.53      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['23', '57'])).
% 0.17/0.53  thf('64', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | ~ (v2_struct_0 @ sk_A))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('65', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['64'])).
% 0.17/0.53  thf(t46_filter_1, axiom,
% 0.17/0.53    (![A:$i]:
% 0.17/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.17/0.53       ( ![B:$i]:
% 0.17/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.17/0.53             ( l3_lattices @ B ) ) =>
% 0.17/0.53           ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.17/0.53               ( v15_lattices @ A ) & ( v16_lattices @ A ) & 
% 0.17/0.53               ( l3_lattices @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.17/0.53               ( v10_lattices @ B ) & ( v15_lattices @ B ) & 
% 0.17/0.53               ( v16_lattices @ B ) & ( l3_lattices @ B ) ) <=>
% 0.17/0.53             ( ( ~( v2_struct_0 @ ( k7_filter_1 @ A @ B ) ) ) & 
% 0.17/0.53               ( v10_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.53               ( v15_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.53               ( v16_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.17/0.53               ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) ))).
% 0.17/0.53  thf('66', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v10_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (l3_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | (v16_lattices @ X7)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7))),
% 0.17/0.53      inference('cnf', [status(esa)], [t46_filter_1])).
% 0.17/0.53  thf('67', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v10_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)
% 0.17/0.53         | (v16_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (l3_lattices @ sk_B)
% 0.17/0.53         | ~ (v10_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.17/0.53  thf('68', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('69', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('70', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('71', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('72', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('73', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | (v16_lattices @ sk_A)
% 0.17/0.53         | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['67', '68', '69', '70', '71', '72'])).
% 0.17/0.53  thf('74', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v16_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['63', '73'])).
% 0.17/0.53  thf('75', plain,
% 0.17/0.53      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['1'])).
% 0.17/0.53  thf('76', plain,
% 0.17/0.53      (![X0 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v17_lattices @ X0)
% 0.17/0.53          | (v16_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.53  thf('77', plain,
% 0.17/0.53      ((~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['4'])).
% 0.17/0.53  thf('78', plain,
% 0.17/0.53      (((~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['76', '77'])).
% 0.17/0.53  thf('79', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('80', plain,
% 0.17/0.53      ((((v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['78', '79'])).
% 0.17/0.53  thf('81', plain,
% 0.17/0.53      (((v16_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['75', '80'])).
% 0.17/0.53  thf('82', plain, (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)], ['25', '27', '56'])).
% 0.17/0.53  thf('83', plain,
% 0.17/0.53      (((v16_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.17/0.53  thf('84', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v16_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['74', '83'])).
% 0.17/0.53  thf('85', plain,
% 0.17/0.53      ((~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['4'])).
% 0.17/0.53  thf('86', plain, (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)], ['25', '27', '56'])).
% 0.17/0.53  thf('87', plain, (~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.17/0.53  thf('88', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A) | (v16_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['84', '87'])).
% 0.17/0.53  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('90', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B) | (v16_lattices @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['88', '89'])).
% 0.17/0.53  thf('91', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('92', plain,
% 0.17/0.53      (((v16_lattices @ sk_A))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['90', '91'])).
% 0.17/0.53  thf(cc6_lattices, axiom,
% 0.17/0.53    (![A:$i]:
% 0.17/0.53     ( ( l3_lattices @ A ) =>
% 0.17/0.53       ( ( ( ~( v2_struct_0 @ A ) ) & ( v11_lattices @ A ) & 
% 0.17/0.53           ( v15_lattices @ A ) & ( v16_lattices @ A ) ) =>
% 0.17/0.53         ( ( ~( v2_struct_0 @ A ) ) & ( v17_lattices @ A ) ) ) ))).
% 0.17/0.53  thf('93', plain,
% 0.17/0.53      (![X1 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | (v17_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc6_lattices])).
% 0.17/0.53  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('95', plain,
% 0.17/0.53      ((~ (l3_lattices @ sk_A)
% 0.17/0.53        | (v17_lattices @ sk_A)
% 0.17/0.53        | ~ (v16_lattices @ sk_A)
% 0.17/0.53        | ~ (v15_lattices @ sk_A)
% 0.17/0.53        | ~ (v11_lattices @ sk_A))),
% 0.17/0.53      inference('sup-', [status(thm)], ['93', '94'])).
% 0.17/0.53  thf('96', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('97', plain,
% 0.17/0.53      (((v17_lattices @ sk_A)
% 0.17/0.53        | ~ (v16_lattices @ sk_A)
% 0.17/0.53        | ~ (v15_lattices @ sk_A)
% 0.17/0.53        | ~ (v11_lattices @ sk_A))),
% 0.17/0.53      inference('demod', [status(thm)], ['95', '96'])).
% 0.17/0.53  thf('98', plain,
% 0.17/0.53      (((~ (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (v15_lattices @ sk_A)
% 0.17/0.53         | (v17_lattices @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['92', '97'])).
% 0.17/0.53  thf('99', plain,
% 0.17/0.53      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['1'])).
% 0.17/0.53  thf('100', plain,
% 0.17/0.53      (![X0 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v17_lattices @ X0)
% 0.17/0.53          | (v11_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.53  thf('101', plain,
% 0.17/0.53      ((~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['4'])).
% 0.17/0.53  thf('102', plain,
% 0.17/0.53      (((~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v11_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['100', '101'])).
% 0.17/0.53  thf('103', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('104', plain,
% 0.17/0.53      ((((v11_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['102', '103'])).
% 0.17/0.53  thf('105', plain,
% 0.17/0.53      (((v11_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['99', '104'])).
% 0.17/0.53  thf('106', plain, (~ ((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)], ['25', '27', '56'])).
% 0.17/0.53  thf('107', plain,
% 0.17/0.53      (((v11_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.17/0.53  thf('108', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['64'])).
% 0.17/0.53  thf('109', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (v10_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (l3_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | (v11_lattices @ X5)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5))),
% 0.17/0.53      inference('cnf', [status(esa)], [t39_filter_1])).
% 0.17/0.53  thf('110', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v10_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)
% 0.17/0.53         | (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v11_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (l3_lattices @ sk_B)
% 0.17/0.53         | ~ (v10_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['108', '109'])).
% 0.17/0.53  thf('111', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('112', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('113', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('114', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('115', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('116', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)],
% 0.17/0.53                ['110', '111', '112', '113', '114', '115'])).
% 0.17/0.53  thf('117', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v11_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['107', '116'])).
% 0.17/0.53  thf('118', plain, (~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.17/0.53  thf('119', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A) | (v11_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['117', '118'])).
% 0.17/0.53  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('121', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B) | (v11_lattices @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['119', '120'])).
% 0.17/0.53  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('123', plain,
% 0.17/0.53      (((v11_lattices @ sk_A))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['121', '122'])).
% 0.17/0.53  thf('124', plain,
% 0.17/0.53      (((v16_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.17/0.53  thf('125', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['64'])).
% 0.17/0.53  thf('126', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v10_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (l3_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | (v15_lattices @ X7)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7))),
% 0.17/0.53      inference('cnf', [status(esa)], [t46_filter_1])).
% 0.17/0.53  thf('127', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v10_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)
% 0.17/0.53         | (v15_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (l3_lattices @ sk_B)
% 0.17/0.53         | ~ (v10_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['125', '126'])).
% 0.17/0.53  thf('128', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('129', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('130', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('131', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('132', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('133', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | (v15_lattices @ sk_A)
% 0.17/0.53         | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)],
% 0.17/0.53                ['127', '128', '129', '130', '131', '132'])).
% 0.17/0.53  thf('134', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v15_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['124', '133'])).
% 0.17/0.53  thf('135', plain,
% 0.17/0.53      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['23', '57'])).
% 0.17/0.53  thf('136', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v15_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['134', '135'])).
% 0.17/0.53  thf('137', plain, (~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.17/0.53  thf('138', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A) | (v15_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['136', '137'])).
% 0.17/0.53  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('140', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B) | (v15_lattices @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['138', '139'])).
% 0.17/0.53  thf('141', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('142', plain,
% 0.17/0.53      (((v15_lattices @ sk_A))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['140', '141'])).
% 0.17/0.53  thf('143', plain,
% 0.17/0.53      (((v17_lattices @ sk_A))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['98', '123', '142'])).
% 0.17/0.53  thf('144', plain, ((~ (v17_lattices @ sk_A)) <= (~ ((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('split', [status(esa)], ['10'])).
% 0.17/0.53  thf('145', plain,
% 0.17/0.53      (((v17_lattices @ sk_A)) | 
% 0.17/0.53       ~ ((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | 
% 0.17/0.53       ~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['143', '144'])).
% 0.17/0.53  thf('146', plain, (((v11_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['28', '33'])).
% 0.17/0.53  thf('147', plain, (((v17_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('split', [status(esa)], ['24'])).
% 0.17/0.53  thf('148', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | ~ (v11_lattices @ X5)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | ~ (v11_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | (v10_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5))),
% 0.17/0.53      inference('cnf', [status(esa)], [t39_filter_1])).
% 0.17/0.53  thf('149', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         ((v10_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (v11_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v11_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ X4))),
% 0.17/0.53      inference('simplify', [status(thm)], ['148'])).
% 0.17/0.53  thf('150', plain,
% 0.17/0.53      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['1'])).
% 0.17/0.53  thf('151', plain,
% 0.17/0.53      ((~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (l3_lattices @ sk_B)
% 0.17/0.53        | ~ (v17_lattices @ sk_B)
% 0.17/0.53        | ~ (v10_lattices @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ sk_B)
% 0.17/0.53        | ~ (l3_lattices @ sk_A)
% 0.17/0.53        | ~ (v17_lattices @ sk_A)
% 0.17/0.53        | ~ (v10_lattices @ sk_A)
% 0.17/0.53        | (v2_struct_0 @ sk_A))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('152', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('153', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('154', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('155', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('156', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('157', plain,
% 0.17/0.53      ((~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (v17_lattices @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ sk_B)
% 0.17/0.53        | ~ (v17_lattices @ sk_A)
% 0.17/0.53        | (v2_struct_0 @ sk_A))),
% 0.17/0.53      inference('demod', [status(thm)],
% 0.17/0.53                ['151', '152', '153', '154', '155', '156'])).
% 0.17/0.53  thf('158', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v17_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_B)
% 0.17/0.53         | ~ (v17_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['150', '157'])).
% 0.17/0.53  thf('159', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | ~ (v10_lattices @ sk_B)
% 0.17/0.53         | ~ (l3_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v10_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_B)
% 0.17/0.53         | ~ (v17_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['149', '158'])).
% 0.17/0.53  thf('160', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('161', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('162', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('163', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('164', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_B)
% 0.17/0.53         | ~ (v17_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['159', '160', '161', '162', '163'])).
% 0.17/0.53  thf('165', plain,
% 0.17/0.53      (((~ (v17_lattices @ sk_A)
% 0.17/0.53         | ~ (v17_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | ~ (v11_lattices @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simplify', [status(thm)], ['164'])).
% 0.17/0.53  thf('166', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['147', '165'])).
% 0.17/0.53  thf('167', plain, (((v11_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['35', '40'])).
% 0.17/0.53  thf('168', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v17_lattices @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['166', '167'])).
% 0.17/0.53  thf('169', plain,
% 0.17/0.53      (((~ (v17_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ sk_B)) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['146', '168'])).
% 0.17/0.53  thf('170', plain, (((v17_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('split', [status(esa)], ['26'])).
% 0.17/0.53  thf('171', plain,
% 0.17/0.53      ((((v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ sk_B)) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['169', '170'])).
% 0.17/0.53  thf('172', plain, (~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.17/0.53  thf('173', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ sk_B)) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['171', '172'])).
% 0.17/0.53  thf('174', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('175', plain,
% 0.17/0.53      (((v2_struct_0 @ sk_A))
% 0.17/0.53         <= (((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ sk_B)) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['173', '174'])).
% 0.17/0.53  thf('176', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('177', plain,
% 0.17/0.53      (~ ((v17_lattices @ sk_B)) | 
% 0.17/0.53       ~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | 
% 0.17/0.53       ~ ((v17_lattices @ sk_A))),
% 0.17/0.53      inference('sup-', [status(thm)], ['175', '176'])).
% 0.17/0.53  thf('178', plain, (((v17_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('split', [status(esa)], ['26'])).
% 0.17/0.53  thf('179', plain,
% 0.17/0.53      (![X0 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v17_lattices @ X0)
% 0.17/0.53          | (v16_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.53  thf('180', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('181', plain,
% 0.17/0.53      ((~ (l3_lattices @ sk_B)
% 0.17/0.53        | (v16_lattices @ sk_B)
% 0.17/0.53        | ~ (v17_lattices @ sk_B))),
% 0.17/0.53      inference('sup-', [status(thm)], ['179', '180'])).
% 0.17/0.53  thf('182', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('183', plain, (((v16_lattices @ sk_B) | ~ (v17_lattices @ sk_B))),
% 0.17/0.53      inference('demod', [status(thm)], ['181', '182'])).
% 0.17/0.53  thf('184', plain, (((v16_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['178', '183'])).
% 0.17/0.53  thf('185', plain, (((v11_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['35', '40'])).
% 0.17/0.53  thf('186', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | ~ (v11_lattices @ X5)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | ~ (v11_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | (v11_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5))),
% 0.17/0.53      inference('cnf', [status(esa)], [t39_filter_1])).
% 0.17/0.53  thf('187', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         ((v11_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (v11_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v11_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ X4))),
% 0.17/0.53      inference('simplify', [status(thm)], ['186'])).
% 0.17/0.53  thf('188', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | ~ (v15_lattices @ X7)
% 0.17/0.53          | ~ (v16_lattices @ X7)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (v15_lattices @ X6)
% 0.17/0.53          | ~ (v16_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v15_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7))),
% 0.17/0.53      inference('cnf', [status(esa)], [t46_filter_1])).
% 0.17/0.53  thf('189', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v15_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v16_lattices @ X6)
% 0.17/0.53          | ~ (v15_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v16_lattices @ X7)
% 0.17/0.53          | ~ (v15_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ X6))),
% 0.17/0.53      inference('simplify', [status(thm)], ['188'])).
% 0.17/0.53  thf('190', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | ~ (v15_lattices @ X7)
% 0.17/0.53          | ~ (v16_lattices @ X7)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (v15_lattices @ X6)
% 0.17/0.53          | ~ (v16_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v16_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7))),
% 0.17/0.53      inference('cnf', [status(esa)], [t46_filter_1])).
% 0.17/0.53  thf('191', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v16_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v16_lattices @ X6)
% 0.17/0.53          | ~ (v15_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v16_lattices @ X7)
% 0.17/0.53          | ~ (v15_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ X6))),
% 0.17/0.53      inference('simplify', [status(thm)], ['190'])).
% 0.17/0.53  thf('192', plain,
% 0.17/0.53      (![X2 : $i, X3 : $i]:
% 0.17/0.53         (~ (l3_lattices @ X2)
% 0.17/0.53          | (v2_struct_0 @ X2)
% 0.17/0.53          | (v2_struct_0 @ X3)
% 0.17/0.53          | ~ (l3_lattices @ X3)
% 0.17/0.53          | (l3_lattices @ (k7_filter_1 @ X2 @ X3)))),
% 0.17/0.53      inference('cnf', [status(esa)], [dt_k7_filter_1])).
% 0.17/0.53  thf('193', plain,
% 0.17/0.53      (![X1 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | (v17_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc6_lattices])).
% 0.17/0.53  thf('194', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | ~ (v15_lattices @ X7)
% 0.17/0.53          | ~ (v16_lattices @ X7)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (v15_lattices @ X6)
% 0.17/0.53          | ~ (v16_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | ~ (v2_struct_0 @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7))),
% 0.17/0.53      inference('cnf', [status(esa)], [t46_filter_1])).
% 0.17/0.53  thf('195', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         (~ (v2_struct_0 @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v16_lattices @ X6)
% 0.17/0.53          | ~ (v15_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v16_lattices @ X7)
% 0.17/0.53          | ~ (v15_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ X6))),
% 0.17/0.53      inference('simplify', [status(thm)], ['194'])).
% 0.17/0.53  thf('196', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         (~ (l3_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | (v17_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | (v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (v16_lattices @ X0))),
% 0.17/0.53      inference('sup-', [status(thm)], ['193', '195'])).
% 0.17/0.53  thf('197', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         (~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | (v17_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['192', '196'])).
% 0.17/0.53  thf('198', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v17_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | (v2_struct_0 @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('simplify', [status(thm)], ['197'])).
% 0.17/0.53  thf('199', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | (v17_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['191', '198'])).
% 0.17/0.53  thf('200', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v17_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0))),
% 0.17/0.53      inference('simplify', [status(thm)], ['199'])).
% 0.17/0.53  thf('201', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | (v17_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['189', '200'])).
% 0.17/0.53  thf('202', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v17_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0))),
% 0.17/0.53      inference('simplify', [status(thm)], ['201'])).
% 0.17/0.53  thf('203', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | (v17_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['187', '202'])).
% 0.17/0.53  thf('204', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v17_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v16_lattices @ X0)
% 0.17/0.53          | ~ (v15_lattices @ X0)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0))),
% 0.17/0.53      inference('simplify', [status(thm)], ['203'])).
% 0.17/0.53  thf('205', plain,
% 0.17/0.53      ((~ (v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['10'])).
% 0.17/0.53  thf('206', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | ~ (v10_lattices @ sk_B)
% 0.17/0.53         | ~ (l3_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v10_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | ~ (v15_lattices @ sk_A)
% 0.17/0.53         | ~ (v16_lattices @ sk_A)
% 0.17/0.53         | ~ (v15_lattices @ sk_B)
% 0.17/0.53         | ~ (v16_lattices @ sk_B)))
% 0.17/0.53         <= (~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['204', '205'])).
% 0.17/0.53  thf('207', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('208', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('209', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('210', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('211', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | ~ (v15_lattices @ sk_A)
% 0.17/0.53         | ~ (v16_lattices @ sk_A)
% 0.17/0.53         | ~ (v15_lattices @ sk_B)
% 0.17/0.53         | ~ (v16_lattices @ sk_B)))
% 0.17/0.53         <= (~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['206', '207', '208', '209', '210'])).
% 0.17/0.53  thf('212', plain,
% 0.17/0.53      (((~ (v16_lattices @ sk_B)
% 0.17/0.53         | ~ (v15_lattices @ sk_B)
% 0.17/0.53         | ~ (v16_lattices @ sk_A)
% 0.17/0.53         | ~ (v15_lattices @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['185', '211'])).
% 0.17/0.53  thf('213', plain, (((v17_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('split', [status(esa)], ['24'])).
% 0.17/0.53  thf('214', plain,
% 0.17/0.53      (![X0 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v17_lattices @ X0)
% 0.17/0.53          | (v16_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.53  thf('215', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('216', plain,
% 0.17/0.53      ((~ (l3_lattices @ sk_A)
% 0.17/0.53        | (v16_lattices @ sk_A)
% 0.17/0.53        | ~ (v17_lattices @ sk_A))),
% 0.17/0.53      inference('sup-', [status(thm)], ['214', '215'])).
% 0.17/0.53  thf('217', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('218', plain, (((v16_lattices @ sk_A) | ~ (v17_lattices @ sk_A))),
% 0.17/0.53      inference('demod', [status(thm)], ['216', '217'])).
% 0.17/0.53  thf('219', plain, (((v16_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['213', '218'])).
% 0.17/0.53  thf('220', plain, (((v17_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('split', [status(esa)], ['24'])).
% 0.17/0.53  thf('221', plain,
% 0.17/0.53      (![X0 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v17_lattices @ X0)
% 0.17/0.53          | (v15_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.53  thf('222', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('223', plain,
% 0.17/0.53      ((~ (l3_lattices @ sk_A)
% 0.17/0.53        | (v15_lattices @ sk_A)
% 0.17/0.53        | ~ (v17_lattices @ sk_A))),
% 0.17/0.53      inference('sup-', [status(thm)], ['221', '222'])).
% 0.17/0.53  thf('224', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('225', plain, (((v15_lattices @ sk_A) | ~ (v17_lattices @ sk_A))),
% 0.17/0.53      inference('demod', [status(thm)], ['223', '224'])).
% 0.17/0.53  thf('226', plain, (((v15_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['220', '225'])).
% 0.17/0.53  thf('227', plain,
% 0.17/0.53      (((~ (v16_lattices @ sk_B)
% 0.17/0.53         | ~ (v15_lattices @ sk_B)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('demod', [status(thm)], ['212', '219', '226'])).
% 0.17/0.53  thf('228', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v11_lattices @ sk_B)
% 0.17/0.53         | ~ (v15_lattices @ sk_B)))
% 0.17/0.53         <= (~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['184', '227'])).
% 0.17/0.53  thf('229', plain, (((v11_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['28', '33'])).
% 0.17/0.53  thf('230', plain, (((v17_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('split', [status(esa)], ['26'])).
% 0.17/0.53  thf('231', plain,
% 0.17/0.53      (![X0 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v17_lattices @ X0)
% 0.17/0.53          | (v15_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.17/0.53  thf('232', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('233', plain,
% 0.17/0.53      ((~ (l3_lattices @ sk_B)
% 0.17/0.53        | (v15_lattices @ sk_B)
% 0.17/0.53        | ~ (v17_lattices @ sk_B))),
% 0.17/0.53      inference('sup-', [status(thm)], ['231', '232'])).
% 0.17/0.53  thf('234', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('235', plain, (((v15_lattices @ sk_B) | ~ (v17_lattices @ sk_B))),
% 0.17/0.53      inference('demod', [status(thm)], ['233', '234'])).
% 0.17/0.53  thf('236', plain, (((v15_lattices @ sk_B)) <= (((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['230', '235'])).
% 0.17/0.53  thf('237', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('demod', [status(thm)], ['228', '229', '236'])).
% 0.17/0.53  thf('238', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('239', plain,
% 0.17/0.53      (((v2_struct_0 @ sk_A))
% 0.17/0.53         <= (~ ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ sk_A)) & 
% 0.17/0.53             ((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('clc', [status(thm)], ['237', '238'])).
% 0.17/0.53  thf('240', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('241', plain,
% 0.17/0.53      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | 
% 0.17/0.53       ~ ((v17_lattices @ sk_B)) | ~ ((v17_lattices @ sk_A))),
% 0.17/0.53      inference('sup-', [status(thm)], ['239', '240'])).
% 0.17/0.53  thf('242', plain,
% 0.17/0.53      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v17_lattices @ sk_B))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('243', plain,
% 0.17/0.53      (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | ((v17_lattices @ sk_B))),
% 0.17/0.53      inference('split', [status(esa)], ['242'])).
% 0.17/0.53  thf('244', plain, (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)],
% 0.17/0.53                ['60', '62', '145', '177', '241', '243'])).
% 0.17/0.53  thf('245', plain, ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['58', '244'])).
% 0.17/0.53  thf('246', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         ((v10_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (v11_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v11_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ X4))),
% 0.17/0.53      inference('simplify', [status(thm)], ['148'])).
% 0.17/0.53  thf('247', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v10_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (l3_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | (v16_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7))),
% 0.17/0.53      inference('cnf', [status(esa)], [t46_filter_1])).
% 0.17/0.53  thf('248', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | (v16_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | (v2_struct_0 @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0))),
% 0.17/0.53      inference('sup-', [status(thm)], ['246', '247'])).
% 0.17/0.53  thf('249', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((v2_struct_0 @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | ~ (l3_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.17/0.53          | (v16_lattices @ X0)
% 0.17/0.53          | ~ (v11_lattices @ X0)
% 0.17/0.53          | ~ (l3_lattices @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X1)
% 0.17/0.53          | ~ (v10_lattices @ X1)
% 0.17/0.53          | (v2_struct_0 @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X0)
% 0.17/0.53          | ~ (v10_lattices @ X0)
% 0.17/0.53          | (v2_struct_0 @ X0))),
% 0.17/0.53      inference('simplify', [status(thm)], ['248'])).
% 0.17/0.53  thf('250', plain,
% 0.17/0.53      (((v2_struct_0 @ sk_B)
% 0.17/0.53        | ~ (v10_lattices @ sk_B)
% 0.17/0.53        | ~ (l3_lattices @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ sk_A)
% 0.17/0.53        | ~ (v10_lattices @ sk_A)
% 0.17/0.53        | ~ (v11_lattices @ sk_A)
% 0.17/0.53        | ~ (l3_lattices @ sk_A)
% 0.17/0.53        | ~ (v11_lattices @ sk_B)
% 0.17/0.53        | (v16_lattices @ sk_B)
% 0.17/0.53        | ~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['245', '249'])).
% 0.17/0.53  thf('251', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('252', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('253', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('254', plain, (((v11_lattices @ sk_A)) <= (((v17_lattices @ sk_A)))),
% 0.17/0.53      inference('sup-', [status(thm)], ['35', '40'])).
% 0.17/0.53  thf('255', plain, (((v17_lattices @ sk_A))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)], ['60', '62', '145'])).
% 0.17/0.53  thf('256', plain, ((v11_lattices @ sk_A)),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['254', '255'])).
% 0.17/0.53  thf('257', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('258', plain,
% 0.17/0.53      (((v11_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.17/0.53  thf('259', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['64'])).
% 0.17/0.53  thf('260', plain,
% 0.17/0.53      (![X4 : $i, X5 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X4)
% 0.17/0.53          | ~ (v10_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X4)
% 0.17/0.53          | (v2_struct_0 @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (v10_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (v11_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | ~ (l3_lattices @ (k7_filter_1 @ X5 @ X4))
% 0.17/0.53          | (v11_lattices @ X4)
% 0.17/0.53          | ~ (l3_lattices @ X5)
% 0.17/0.53          | ~ (v10_lattices @ X5)
% 0.17/0.53          | (v2_struct_0 @ X5))),
% 0.17/0.53      inference('cnf', [status(esa)], [t39_filter_1])).
% 0.17/0.53  thf('261', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v10_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)
% 0.17/0.53         | (v11_lattices @ sk_B)
% 0.17/0.53         | ~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v11_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (l3_lattices @ sk_B)
% 0.17/0.53         | ~ (v10_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['259', '260'])).
% 0.17/0.53  thf('262', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('263', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('264', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('265', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('266', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('267', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | (v11_lattices @ sk_B)
% 0.17/0.53         | ~ (v11_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)],
% 0.17/0.53                ['261', '262', '263', '264', '265', '266'])).
% 0.17/0.53  thf('268', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v11_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['258', '267'])).
% 0.17/0.53  thf('269', plain, (~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.17/0.53  thf('270', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A) | (v11_lattices @ sk_B) | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['268', '269'])).
% 0.17/0.53  thf('271', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('272', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B) | (v11_lattices @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['270', '271'])).
% 0.17/0.53  thf('273', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('274', plain,
% 0.17/0.53      (((v11_lattices @ sk_B))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('clc', [status(thm)], ['272', '273'])).
% 0.17/0.53  thf('275', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v17_lattices @ sk_B))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('276', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | ((v17_lattices @ sk_B))),
% 0.17/0.53      inference('split', [status(esa)], ['275'])).
% 0.17/0.53  thf('277', plain, (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)],
% 0.17/0.53                ['60', '62', '145', '177', '241', '276'])).
% 0.17/0.53  thf('278', plain, (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)],
% 0.17/0.53                ['60', '62', '145', '177', '241', '243'])).
% 0.17/0.53  thf('279', plain, ((v11_lattices @ sk_B)),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['274', '277', '278'])).
% 0.17/0.53  thf('280', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('281', plain,
% 0.17/0.53      (((v2_struct_0 @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ sk_A)
% 0.17/0.53        | (v16_lattices @ sk_B)
% 0.17/0.53        | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('demod', [status(thm)],
% 0.17/0.53                ['250', '251', '252', '253', '256', '257', '279', '280'])).
% 0.17/0.53  thf('282', plain,
% 0.17/0.53      (((v16_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.17/0.53  thf('283', plain, (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)],
% 0.17/0.53                ['60', '62', '145', '177', '241', '243'])).
% 0.17/0.53  thf('284', plain, ((v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['282', '283'])).
% 0.17/0.53  thf('285', plain,
% 0.17/0.53      (((v2_struct_0 @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ sk_A)
% 0.17/0.53        | (v16_lattices @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('demod', [status(thm)], ['281', '284'])).
% 0.17/0.53  thf('286', plain, (~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.17/0.53  thf('287', plain,
% 0.17/0.53      (((v16_lattices @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.17/0.53      inference('sup-', [status(thm)], ['285', '286'])).
% 0.17/0.53  thf('288', plain,
% 0.17/0.53      (![X1 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X1)
% 0.17/0.53          | ~ (v11_lattices @ X1)
% 0.17/0.53          | ~ (v15_lattices @ X1)
% 0.17/0.53          | ~ (v16_lattices @ X1)
% 0.17/0.53          | (v17_lattices @ X1)
% 0.17/0.53          | ~ (l3_lattices @ X1))),
% 0.17/0.53      inference('cnf', [status(esa)], [cc6_lattices])).
% 0.17/0.53  thf('289', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('290', plain,
% 0.17/0.53      ((~ (l3_lattices @ sk_B)
% 0.17/0.53        | (v17_lattices @ sk_B)
% 0.17/0.53        | ~ (v16_lattices @ sk_B)
% 0.17/0.53        | ~ (v15_lattices @ sk_B)
% 0.17/0.53        | ~ (v11_lattices @ sk_B))),
% 0.17/0.53      inference('sup-', [status(thm)], ['288', '289'])).
% 0.17/0.53  thf('291', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('292', plain,
% 0.17/0.53      (((v17_lattices @ sk_B)
% 0.17/0.53        | ~ (v16_lattices @ sk_B)
% 0.17/0.53        | ~ (v15_lattices @ sk_B)
% 0.17/0.53        | ~ (v11_lattices @ sk_B))),
% 0.17/0.53      inference('demod', [status(thm)], ['290', '291'])).
% 0.17/0.53  thf('293', plain, ((v11_lattices @ sk_B)),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['274', '277', '278'])).
% 0.17/0.53  thf('294', plain,
% 0.17/0.53      (((v17_lattices @ sk_B)
% 0.17/0.53        | ~ (v16_lattices @ sk_B)
% 0.17/0.53        | ~ (v15_lattices @ sk_B))),
% 0.17/0.53      inference('demod', [status(thm)], ['292', '293'])).
% 0.17/0.53  thf('295', plain, ((~ (v17_lattices @ sk_B)) <= (~ ((v17_lattices @ sk_B)))),
% 0.17/0.53      inference('split', [status(esa)], ['10'])).
% 0.17/0.53  thf('296', plain, (~ ((v17_lattices @ sk_B))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)],
% 0.17/0.53                ['60', '62', '145', '177', '241'])).
% 0.17/0.53  thf('297', plain, (~ (v17_lattices @ sk_B)),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['295', '296'])).
% 0.17/0.53  thf('298', plain, ((~ (v15_lattices @ sk_B) | ~ (v16_lattices @ sk_B))),
% 0.17/0.53      inference('clc', [status(thm)], ['294', '297'])).
% 0.17/0.53  thf('299', plain,
% 0.17/0.53      (((v16_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.17/0.53  thf('300', plain,
% 0.17/0.53      (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('split', [status(esa)], ['64'])).
% 0.17/0.53  thf('301', plain,
% 0.17/0.53      (![X6 : $i, X7 : $i]:
% 0.17/0.53         ((v2_struct_0 @ X6)
% 0.17/0.53          | ~ (v10_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X6)
% 0.17/0.53          | (v2_struct_0 @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v10_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v15_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (v16_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | ~ (l3_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.17/0.53          | (v15_lattices @ X6)
% 0.17/0.53          | ~ (l3_lattices @ X7)
% 0.17/0.53          | ~ (v10_lattices @ X7)
% 0.17/0.53          | (v2_struct_0 @ X7))),
% 0.17/0.53      inference('cnf', [status(esa)], [t46_filter_1])).
% 0.17/0.53  thf('302', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | ~ (v10_lattices @ sk_A)
% 0.17/0.53         | ~ (l3_lattices @ sk_A)
% 0.17/0.53         | (v15_lattices @ sk_B)
% 0.17/0.53         | ~ (l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (l3_lattices @ sk_B)
% 0.17/0.53         | ~ (v10_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['300', '301'])).
% 0.17/0.53  thf('303', plain, ((v10_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('304', plain, ((l3_lattices @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('305', plain, ((l3_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['8', '20'])).
% 0.17/0.53  thf('306', plain, ((l3_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('307', plain, ((v10_lattices @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('308', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_A)
% 0.17/0.53         | (v15_lattices @ sk_B)
% 0.17/0.53         | ~ (v16_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v2_struct_0 @ sk_B)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)],
% 0.17/0.53                ['302', '303', '304', '305', '306', '307'])).
% 0.17/0.53  thf('309', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | ~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v15_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('sup-', [status(thm)], ['299', '308'])).
% 0.17/0.53  thf('310', plain,
% 0.17/0.53      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.17/0.53         <= (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['23', '57'])).
% 0.17/0.53  thf('311', plain,
% 0.17/0.53      ((((v2_struct_0 @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53         | (v15_lattices @ sk_B)
% 0.17/0.53         | (v2_struct_0 @ sk_A)))
% 0.17/0.53         <= (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.17/0.53             ((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.17/0.53      inference('demod', [status(thm)], ['309', '310'])).
% 0.17/0.53  thf('312', plain, (((v10_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)],
% 0.17/0.53                ['60', '62', '145', '177', '241', '276'])).
% 0.17/0.53  thf('313', plain, (((v17_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.17/0.53      inference('sat_resolution*', [status(thm)],
% 0.17/0.53                ['60', '62', '145', '177', '241', '243'])).
% 0.17/0.53  thf('314', plain,
% 0.17/0.53      (((v2_struct_0 @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))
% 0.17/0.53        | (v15_lattices @ sk_B)
% 0.17/0.53        | (v2_struct_0 @ sk_A))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['311', '312', '313'])).
% 0.17/0.53  thf('315', plain, (~ (v2_struct_0 @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.17/0.53      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.17/0.53  thf('316', plain,
% 0.17/0.53      (((v2_struct_0 @ sk_A) | (v15_lattices @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.17/0.53      inference('sup-', [status(thm)], ['314', '315'])).
% 0.17/0.53  thf('317', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('318', plain, (((v2_struct_0 @ sk_B) | (v15_lattices @ sk_B))),
% 0.17/0.53      inference('clc', [status(thm)], ['316', '317'])).
% 0.17/0.53  thf('319', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('320', plain, ((v15_lattices @ sk_B)),
% 0.17/0.53      inference('clc', [status(thm)], ['318', '319'])).
% 0.17/0.53  thf('321', plain, (~ (v16_lattices @ sk_B)),
% 0.17/0.53      inference('demod', [status(thm)], ['298', '320'])).
% 0.17/0.53  thf('322', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.17/0.53      inference('clc', [status(thm)], ['287', '321'])).
% 0.17/0.53  thf('323', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf('324', plain, ((v2_struct_0 @ sk_A)),
% 0.17/0.53      inference('clc', [status(thm)], ['322', '323'])).
% 0.17/0.53  thf('325', plain, ($false), inference('demod', [status(thm)], ['0', '324'])).
% 0.17/0.53  
% 0.17/0.53  % SZS output end Refutation
% 0.17/0.53  
% 0.17/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
