%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B6CWA5rial

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 861 expanded)
%              Number of leaves         :   17 ( 238 expanded)
%              Depth                    :   23
%              Number of atoms          : 1397 (11393 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k7_filter_1_type,type,(
    k7_filter_1: $i > $i > $i )).

thf(v15_lattices_type,type,(
    v15_lattices: $i > $o )).

thf(cc3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v13_lattices @ A )
          & ( v14_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v15_lattices @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc3_lattices])).

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

thf('1',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v15_lattices @ sk_B )
    | ~ ( v14_lattices @ sk_B )
    | ~ ( v13_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v15_lattices @ sk_B )
    | ~ ( v14_lattices @ sk_B )
    | ~ ( v13_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v15_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf(dt_k7_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) )
        & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( l3_lattices @ ( k7_filter_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf(cc4_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v15_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v13_lattices @ A )
          & ( v14_lattices @ A ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf(fc2_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
        & ( v3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ( v13_lattices @ X6 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_filter_1])).

thf('22',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v13_lattices @ sk_B )
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
      | ( v13_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v13_lattices @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v13_lattices @ sk_B )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v15_lattices @ sk_A )
    | ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('33',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( l3_lattices @ ( k7_filter_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ( v14_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v14_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v14_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v14_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v14_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ( v14_lattices @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t41_filter_1])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v14_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v14_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v14_lattices @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v14_lattices @ sk_A )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc3_lattices])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v15_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v15_lattices @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( v13_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ( v13_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_filter_1])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v13_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v13_lattices @ sk_A ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v13_lattices @ sk_A )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','76'])).

thf('78',plain,
    ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( v15_lattices @ sk_A )
   <= ~ ( v15_lattices @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,
    ( ( v15_lattices @ sk_A )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,
    ( ~ ( v15_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['78'])).

thf('82',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v15_lattices @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('83',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ( v14_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v14_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v14_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v14_lattices @ sk_A )
   <= ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v15_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v15_lattices @ sk_B ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v13_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v13_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v13_lattices @ sk_B )
   <= ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v13_lattices @ X7 )
      | ~ ( v13_lattices @ X6 )
      | ( v13_lattices @ ( k7_filter_1 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_filter_1])).

thf('98',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v14_lattices @ X9 )
      | ~ ( v14_lattices @ X8 )
      | ( v14_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t41_filter_1])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( l3_lattices @ ( k7_filter_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc3_lattices])).

thf('101',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v14_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v14_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v14_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v14_lattices @ X0 )
      | ~ ( v14_lattices @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v13_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v14_lattices @ X1 )
      | ~ ( v14_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
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
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,(
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
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['78'])).

thf('110',plain,
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
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_B )
      | ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v14_lattices @ sk_B )
      | ~ ( v14_lattices @ sk_A ) )
   <= ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,
    ( ( ~ ( v14_lattices @ sk_A )
      | ~ ( v14_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','115'])).

thf('117',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v15_lattices @ sk_B ) ),
    inference(split,[status(esa)],['89'])).

thf('118',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ( v14_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v14_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v14_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v14_lattices @ sk_B )
   <= ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,
    ( ( ~ ( v14_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','123'])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_A )
      & ( v15_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','124'])).

thf('126',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v15_lattices @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('127',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v13_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v13_lattices @ sk_A )
   <= ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_A )
      & ( v15_lattices @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v15_lattices @ sk_A )
      & ( v15_lattices @ sk_B ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v15_lattices @ sk_B ) ),
    inference(split,[status(esa)],['89'])).

thf('139',plain,(
    v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['32','80','81','137','138'])).

thf('140',plain,(
    v13_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['31','139'])).

thf('141',plain,
    ( ( v15_lattices @ sk_B )
    | ~ ( v14_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['4','140'])).

thf('142',plain,
    ( ~ ( v15_lattices @ sk_B )
   <= ~ ( v15_lattices @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('143',plain,(
    ~ ( v15_lattices @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['32','80','81','137'])).

thf('144',plain,(
    ~ ( v15_lattices @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v14_lattices @ sk_B ) ),
    inference(clc,[status(thm)],['141','144'])).

thf('146',plain,
    ( ( v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('147',plain,(
    v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['32','80','81','137','138'])).

thf('148',plain,(
    v14_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v14_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ( v14_lattices @ X8 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t41_filter_1])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v14_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v14_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['150','151','152','153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v14_lattices @ sk_B ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v14_lattices @ sk_B ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    $false ),
    inference(demod,[status(thm)],['145','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B6CWA5rial
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:59:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 78 iterations in 0.035s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.22/0.50  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.22/0.50  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(k7_filter_1_type, type, k7_filter_1: $i > $i > $i).
% 0.22/0.50  thf(v15_lattices_type, type, v15_lattices: $i > $o).
% 0.22/0.50  thf(cc3_lattices, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l3_lattices @ A ) =>
% 0.22/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v13_lattices @ A ) & 
% 0.22/0.50           ( v14_lattices @ A ) ) =>
% 0.22/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v15_lattices @ A ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v13_lattices @ X0)
% 0.22/0.50          | ~ (v14_lattices @ X0)
% 0.22/0.50          | (v15_lattices @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc3_lattices])).
% 0.22/0.50  thf(t42_filter_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.22/0.50             ( l3_lattices @ B ) ) =>
% 0.22/0.50           ( ( ( v15_lattices @ A ) & ( v15_lattices @ B ) ) <=>
% 0.22/0.50             ( v15_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.22/0.50            ( l3_lattices @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.22/0.50                ( l3_lattices @ B ) ) =>
% 0.22/0.50              ( ( ( v15_lattices @ A ) & ( v15_lattices @ B ) ) <=>
% 0.22/0.50                ( v15_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t42_filter_1])).
% 0.22/0.50  thf('1', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((~ (l3_lattices @ sk_B)
% 0.22/0.50        | (v15_lattices @ sk_B)
% 0.22/0.50        | ~ (v14_lattices @ sk_B)
% 0.22/0.50        | ~ (v13_lattices @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (((v15_lattices @ sk_B)
% 0.22/0.50        | ~ (v14_lattices @ sk_B)
% 0.22/0.50        | ~ (v13_lattices @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v15_lattices @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['5'])).
% 0.22/0.50  thf(dt_k7_filter_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.22/0.50         ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.22/0.50       ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) ) & 
% 0.22/0.50         ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2)
% 0.22/0.50          | (v2_struct_0 @ X3)
% 0.22/0.50          | ~ (l3_lattices @ X3)
% 0.22/0.50          | (l3_lattices @ (k7_filter_1 @ X2 @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k7_filter_1])).
% 0.22/0.50  thf(cc4_lattices, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l3_lattices @ A ) =>
% 0.22/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v15_lattices @ A ) ) =>
% 0.22/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v13_lattices @ A ) & 
% 0.22/0.50           ( v14_lattices @ A ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v15_lattices @ X1)
% 0.22/0.50          | (v13_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc4_lattices])).
% 0.22/0.50  thf(fc2_filter_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.22/0.50         ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.22/0.50       ( ( ~( v2_struct_0 @ ( k7_filter_1 @ A @ B ) ) ) & 
% 0.22/0.50         ( v3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X4)
% 0.22/0.50          | (v2_struct_0 @ X4)
% 0.22/0.50          | (v2_struct_0 @ X5)
% 0.22/0.50          | ~ (l3_lattices @ X5)
% 0.22/0.50          | ~ (v2_struct_0 @ (k7_filter_1 @ X4 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc2_filter_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l3_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | (v13_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (((~ (l3_lattices @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_A)
% 0.22/0.50         | (v13_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '12'])).
% 0.22/0.50  thf('14', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | (v13_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.50  thf('17', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((((v13_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (((v13_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf(t40_filter_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.22/0.50             ( l3_lattices @ B ) ) =>
% 0.22/0.50           ( ( ( v13_lattices @ A ) & ( v13_lattices @ B ) ) <=>
% 0.22/0.50             ( v13_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X6)
% 0.22/0.50          | ~ (v10_lattices @ X6)
% 0.22/0.50          | ~ (l3_lattices @ X6)
% 0.22/0.50          | ~ (v13_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.22/0.50          | (v13_lattices @ X6)
% 0.22/0.50          | ~ (l3_lattices @ X7)
% 0.22/0.50          | ~ (v10_lattices @ X7)
% 0.22/0.50          | (v2_struct_0 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t40_filter_1])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | ~ (v10_lattices @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_A)
% 0.22/0.50         | (v13_lattices @ sk_B)
% 0.22/0.50         | ~ (l3_lattices @ sk_B)
% 0.22/0.50         | ~ (v10_lattices @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain, ((v10_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('25', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('26', plain, ((v10_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v13_lattices @ sk_B) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.22/0.50  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B) | (v13_lattices @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((v13_lattices @ sk_B))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (((v15_lattices @ sk_A)) | ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['5'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['5'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2)
% 0.22/0.50          | (v2_struct_0 @ X3)
% 0.22/0.50          | ~ (l3_lattices @ X3)
% 0.22/0.50          | (l3_lattices @ (k7_filter_1 @ X2 @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k7_filter_1])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v15_lattices @ X1)
% 0.22/0.50          | (v14_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc4_lattices])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X4)
% 0.22/0.50          | (v2_struct_0 @ X4)
% 0.22/0.50          | (v2_struct_0 @ X5)
% 0.22/0.50          | ~ (l3_lattices @ X5)
% 0.22/0.50          | ~ (v2_struct_0 @ (k7_filter_1 @ X4 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc2_filter_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l3_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | (v14_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | (v14_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v14_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (((~ (l3_lattices @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_A)
% 0.22/0.50         | (v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['33', '39'])).
% 0.22/0.50  thf('41', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('42', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | (v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.50  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      ((((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf(t41_filter_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.22/0.50             ( l3_lattices @ B ) ) =>
% 0.22/0.50           ( ( ( v14_lattices @ A ) & ( v14_lattices @ B ) ) <=>
% 0.22/0.50             ( v14_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X8)
% 0.22/0.50          | ~ (v10_lattices @ X8)
% 0.22/0.50          | ~ (l3_lattices @ X8)
% 0.22/0.50          | ~ (v14_lattices @ (k7_filter_1 @ X9 @ X8))
% 0.22/0.50          | (v14_lattices @ X9)
% 0.22/0.50          | ~ (l3_lattices @ X9)
% 0.22/0.50          | ~ (v10_lattices @ X9)
% 0.22/0.50          | (v2_struct_0 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t41_filter_1])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | ~ (v10_lattices @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_A)
% 0.22/0.50         | (v14_lattices @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_B)
% 0.22/0.50         | ~ (v10_lattices @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.50  thf('50', plain, ((v10_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('51', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('52', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('53', plain, ((v10_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v14_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.22/0.50  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B) | (v14_lattices @ sk_A)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['54', '55'])).
% 0.22/0.50  thf('57', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (((v14_lattices @ sk_A))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v13_lattices @ X0)
% 0.22/0.50          | ~ (v14_lattices @ X0)
% 0.22/0.50          | (v15_lattices @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc3_lattices])).
% 0.22/0.50  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      ((~ (l3_lattices @ sk_A)
% 0.22/0.50        | (v15_lattices @ sk_A)
% 0.22/0.50        | ~ (v14_lattices @ sk_A)
% 0.22/0.50        | ~ (v13_lattices @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.50  thf('62', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (((v15_lattices @ sk_A)
% 0.22/0.50        | ~ (v14_lattices @ sk_A)
% 0.22/0.50        | ~ (v13_lattices @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      (((~ (v13_lattices @ sk_A) | (v15_lattices @ sk_A)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['58', '63'])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      (((v13_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X6)
% 0.22/0.50          | ~ (v10_lattices @ X6)
% 0.22/0.50          | ~ (l3_lattices @ X6)
% 0.22/0.50          | ~ (v13_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.22/0.50          | (v13_lattices @ X7)
% 0.22/0.50          | ~ (l3_lattices @ X7)
% 0.22/0.50          | ~ (v10_lattices @ X7)
% 0.22/0.50          | (v2_struct_0 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t40_filter_1])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | ~ (v10_lattices @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_A)
% 0.22/0.50         | (v13_lattices @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_B)
% 0.22/0.50         | ~ (v10_lattices @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.50  thf('68', plain, ((v10_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('69', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('70', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('71', plain, ((v10_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v13_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.22/0.50  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B) | (v13_lattices @ sk_A)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['72', '73'])).
% 0.22/0.50  thf('75', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      (((v13_lattices @ sk_A))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['74', '75'])).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      (((v15_lattices @ sk_A))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['64', '76'])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      ((~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))
% 0.22/0.50        | ~ (v15_lattices @ sk_B)
% 0.22/0.50        | ~ (v15_lattices @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('79', plain, ((~ (v15_lattices @ sk_A)) <= (~ ((v15_lattices @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['78'])).
% 0.22/0.50  thf('80', plain,
% 0.22/0.50      (((v15_lattices @ sk_A)) | 
% 0.22/0.50       ~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['77', '79'])).
% 0.22/0.50  thf('81', plain,
% 0.22/0.50      (~ ((v15_lattices @ sk_B)) | ~ ((v15_lattices @ sk_A)) | 
% 0.22/0.50       ~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['78'])).
% 0.22/0.50  thf('82', plain, (((v15_lattices @ sk_A)) <= (((v15_lattices @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['5'])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      (![X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v15_lattices @ X1)
% 0.22/0.50          | (v14_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc4_lattices])).
% 0.22/0.50  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('85', plain,
% 0.22/0.50      ((~ (l3_lattices @ sk_A)
% 0.22/0.50        | (v14_lattices @ sk_A)
% 0.22/0.50        | ~ (v15_lattices @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['83', '84'])).
% 0.22/0.50  thf('86', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('87', plain, (((v14_lattices @ sk_A) | ~ (v15_lattices @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['85', '86'])).
% 0.22/0.50  thf('88', plain, (((v14_lattices @ sk_A)) <= (((v15_lattices @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['82', '87'])).
% 0.22/0.50  thf('89', plain,
% 0.22/0.50      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)) | (v15_lattices @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('90', plain, (((v15_lattices @ sk_B)) <= (((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['89'])).
% 0.22/0.50  thf('91', plain,
% 0.22/0.50      (![X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v15_lattices @ X1)
% 0.22/0.50          | (v13_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc4_lattices])).
% 0.22/0.50  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('93', plain,
% 0.22/0.50      ((~ (l3_lattices @ sk_B)
% 0.22/0.50        | (v13_lattices @ sk_B)
% 0.22/0.50        | ~ (v15_lattices @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.22/0.50  thf('94', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('95', plain, (((v13_lattices @ sk_B) | ~ (v15_lattices @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['93', '94'])).
% 0.22/0.50  thf('96', plain, (((v13_lattices @ sk_B)) <= (((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['90', '95'])).
% 0.22/0.50  thf('97', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X6)
% 0.22/0.50          | ~ (v10_lattices @ X6)
% 0.22/0.50          | ~ (l3_lattices @ X6)
% 0.22/0.50          | ~ (v13_lattices @ X7)
% 0.22/0.50          | ~ (v13_lattices @ X6)
% 0.22/0.50          | (v13_lattices @ (k7_filter_1 @ X7 @ X6))
% 0.22/0.50          | ~ (l3_lattices @ X7)
% 0.22/0.50          | ~ (v10_lattices @ X7)
% 0.22/0.50          | (v2_struct_0 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t40_filter_1])).
% 0.22/0.50  thf('98', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X8)
% 0.22/0.50          | ~ (v10_lattices @ X8)
% 0.22/0.50          | ~ (l3_lattices @ X8)
% 0.22/0.50          | ~ (v14_lattices @ X9)
% 0.22/0.50          | ~ (v14_lattices @ X8)
% 0.22/0.50          | (v14_lattices @ (k7_filter_1 @ X9 @ X8))
% 0.22/0.50          | ~ (l3_lattices @ X9)
% 0.22/0.50          | ~ (v10_lattices @ X9)
% 0.22/0.50          | (v2_struct_0 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t41_filter_1])).
% 0.22/0.50  thf('99', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2)
% 0.22/0.50          | (v2_struct_0 @ X3)
% 0.22/0.50          | ~ (l3_lattices @ X3)
% 0.22/0.50          | (l3_lattices @ (k7_filter_1 @ X2 @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k7_filter_1])).
% 0.22/0.50  thf('100', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v13_lattices @ X0)
% 0.22/0.50          | ~ (v14_lattices @ X0)
% 0.22/0.50          | (v15_lattices @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc3_lattices])).
% 0.22/0.50  thf('101', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X4)
% 0.22/0.50          | (v2_struct_0 @ X4)
% 0.22/0.50          | (v2_struct_0 @ X5)
% 0.22/0.50          | ~ (l3_lattices @ X5)
% 0.22/0.50          | ~ (v2_struct_0 @ (k7_filter_1 @ X4 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc2_filter_1])).
% 0.22/0.50  thf('102', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l3_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | (v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v14_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['100', '101'])).
% 0.22/0.50  thf('103', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l3_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | ~ (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v14_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | (v15_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['99', '102'])).
% 0.22/0.50  thf('104', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v14_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['103'])).
% 0.22/0.50  thf('105', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v10_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (v14_lattices @ X0)
% 0.22/0.50          | ~ (v14_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | ~ (v10_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | (v15_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['98', '104'])).
% 0.22/0.50  thf('106', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v13_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v10_lattices @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | ~ (v14_lattices @ X1)
% 0.22/0.50          | ~ (v14_lattices @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (v10_lattices @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['105'])).
% 0.22/0.50  thf('107', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v10_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (v13_lattices @ X0)
% 0.22/0.50          | ~ (v13_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | ~ (v10_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v10_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (v14_lattices @ X0)
% 0.22/0.50          | ~ (v14_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | ~ (v10_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v15_lattices @ (k7_filter_1 @ X1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['97', '106'])).
% 0.22/0.50  thf('108', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v15_lattices @ (k7_filter_1 @ X1 @ X0))
% 0.22/0.50          | ~ (v14_lattices @ X1)
% 0.22/0.50          | ~ (v14_lattices @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v10_lattices @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X0)
% 0.22/0.50          | ~ (v13_lattices @ X1)
% 0.22/0.50          | ~ (v13_lattices @ X0)
% 0.22/0.50          | ~ (l3_lattices @ X1)
% 0.22/0.50          | ~ (v10_lattices @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['107'])).
% 0.22/0.50  thf('109', plain,
% 0.22/0.50      ((~ (v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['78'])).
% 0.22/0.50  thf('110', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | ~ (v10_lattices @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_A)
% 0.22/0.50         | ~ (v13_lattices @ sk_B)
% 0.22/0.50         | ~ (v13_lattices @ sk_A)
% 0.22/0.50         | ~ (l3_lattices @ sk_B)
% 0.22/0.50         | ~ (v10_lattices @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | ~ (v14_lattices @ sk_B)
% 0.22/0.50         | ~ (v14_lattices @ sk_A)))
% 0.22/0.50         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['108', '109'])).
% 0.22/0.50  thf('111', plain, ((v10_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('112', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('113', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('114', plain, ((v10_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('115', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | ~ (v13_lattices @ sk_B)
% 0.22/0.50         | ~ (v13_lattices @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | ~ (v14_lattices @ sk_B)
% 0.22/0.50         | ~ (v14_lattices @ sk_A)))
% 0.22/0.50         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.22/0.50  thf('116', plain,
% 0.22/0.50      (((~ (v14_lattices @ sk_A)
% 0.22/0.50         | ~ (v14_lattices @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | ~ (v13_lattices @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.22/0.50             ((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['96', '115'])).
% 0.22/0.50  thf('117', plain, (((v15_lattices @ sk_B)) <= (((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['89'])).
% 0.22/0.50  thf('118', plain,
% 0.22/0.50      (![X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v15_lattices @ X1)
% 0.22/0.50          | (v14_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc4_lattices])).
% 0.22/0.50  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('120', plain,
% 0.22/0.50      ((~ (l3_lattices @ sk_B)
% 0.22/0.50        | (v14_lattices @ sk_B)
% 0.22/0.50        | ~ (v15_lattices @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['118', '119'])).
% 0.22/0.50  thf('121', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('122', plain, (((v14_lattices @ sk_B) | ~ (v15_lattices @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['120', '121'])).
% 0.22/0.50  thf('123', plain, (((v14_lattices @ sk_B)) <= (((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['117', '122'])).
% 0.22/0.50  thf('124', plain,
% 0.22/0.50      (((~ (v14_lattices @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | ~ (v13_lattices @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.22/0.50             ((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['116', '123'])).
% 0.22/0.50  thf('125', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | ~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.22/0.50             ((v15_lattices @ sk_A)) & 
% 0.22/0.50             ((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['88', '124'])).
% 0.22/0.50  thf('126', plain, (((v15_lattices @ sk_A)) <= (((v15_lattices @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['5'])).
% 0.22/0.50  thf('127', plain,
% 0.22/0.50      (![X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (v15_lattices @ X1)
% 0.22/0.50          | (v13_lattices @ X1)
% 0.22/0.50          | ~ (l3_lattices @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc4_lattices])).
% 0.22/0.50  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('129', plain,
% 0.22/0.50      ((~ (l3_lattices @ sk_A)
% 0.22/0.50        | (v13_lattices @ sk_A)
% 0.22/0.50        | ~ (v15_lattices @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['127', '128'])).
% 0.22/0.50  thf('130', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('131', plain, (((v13_lattices @ sk_A) | ~ (v15_lattices @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['129', '130'])).
% 0.22/0.50  thf('132', plain, (((v13_lattices @ sk_A)) <= (((v15_lattices @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['126', '131'])).
% 0.22/0.50  thf('133', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.22/0.50             ((v15_lattices @ sk_A)) & 
% 0.22/0.50             ((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['125', '132'])).
% 0.22/0.50  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('135', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_B))
% 0.22/0.50         <= (~ ((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) & 
% 0.22/0.50             ((v15_lattices @ sk_A)) & 
% 0.22/0.50             ((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('clc', [status(thm)], ['133', '134'])).
% 0.22/0.50  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('137', plain,
% 0.22/0.50      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | 
% 0.22/0.50       ~ ((v15_lattices @ sk_A)) | ~ ((v15_lattices @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['135', '136'])).
% 0.22/0.50  thf('138', plain,
% 0.22/0.50      (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))) | ((v15_lattices @ sk_B))),
% 0.22/0.50      inference('split', [status(esa)], ['89'])).
% 0.22/0.50  thf('139', plain, (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)],
% 0.22/0.50                ['32', '80', '81', '137', '138'])).
% 0.22/0.50  thf('140', plain, ((v13_lattices @ sk_B)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['31', '139'])).
% 0.22/0.50  thf('141', plain, (((v15_lattices @ sk_B) | ~ (v14_lattices @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '140'])).
% 0.22/0.50  thf('142', plain, ((~ (v15_lattices @ sk_B)) <= (~ ((v15_lattices @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['78'])).
% 0.22/0.50  thf('143', plain, (~ ((v15_lattices @ sk_B))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['32', '80', '81', '137'])).
% 0.22/0.50  thf('144', plain, (~ (v15_lattices @ sk_B)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['142', '143'])).
% 0.22/0.50  thf('145', plain, (~ (v14_lattices @ sk_B)),
% 0.22/0.50      inference('clc', [status(thm)], ['141', '144'])).
% 0.22/0.50  thf('146', plain,
% 0.22/0.50      (((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('147', plain, (((v15_lattices @ (k7_filter_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)],
% 0.22/0.50                ['32', '80', '81', '137', '138'])).
% 0.22/0.50  thf('148', plain, ((v14_lattices @ (k7_filter_1 @ sk_A @ sk_B))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['146', '147'])).
% 0.22/0.50  thf('149', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X8)
% 0.22/0.50          | ~ (v10_lattices @ X8)
% 0.22/0.50          | ~ (l3_lattices @ X8)
% 0.22/0.50          | ~ (v14_lattices @ (k7_filter_1 @ X9 @ X8))
% 0.22/0.50          | (v14_lattices @ X8)
% 0.22/0.50          | ~ (l3_lattices @ X9)
% 0.22/0.50          | ~ (v10_lattices @ X9)
% 0.22/0.50          | (v2_struct_0 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t41_filter_1])).
% 0.22/0.50  thf('150', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v10_lattices @ sk_A)
% 0.22/0.50        | ~ (l3_lattices @ sk_A)
% 0.22/0.50        | (v14_lattices @ sk_B)
% 0.22/0.50        | ~ (l3_lattices @ sk_B)
% 0.22/0.50        | ~ (v10_lattices @ sk_B)
% 0.22/0.50        | (v2_struct_0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['148', '149'])).
% 0.22/0.50  thf('151', plain, ((v10_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('152', plain, ((l3_lattices @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('153', plain, ((l3_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('154', plain, ((v10_lattices @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('155', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A) | (v14_lattices @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['150', '151', '152', '153', '154'])).
% 0.22/0.50  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('157', plain, (((v2_struct_0 @ sk_B) | (v14_lattices @ sk_B))),
% 0.22/0.50      inference('clc', [status(thm)], ['155', '156'])).
% 0.22/0.50  thf('158', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('159', plain, ((v14_lattices @ sk_B)),
% 0.22/0.50      inference('clc', [status(thm)], ['157', '158'])).
% 0.22/0.50  thf('160', plain, ($false), inference('demod', [status(thm)], ['145', '159'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
