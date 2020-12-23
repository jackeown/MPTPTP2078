%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1452+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7M1zE76XjH

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  353 (12592 expanded)
%              Number of leaves         :   19 (3295 expanded)
%              Depth                    :   35
%              Number of atoms          : 2961 (300711 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_A_7_type,type,(
    sk_A_7: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k7_filter_1_type,type,(
    k7_filter_1: $i > $i > $i )).

thf(v16_lattices_type,type,(
    v16_lattices: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v15_lattices @ X13 )
      | ~ ( v16_lattices @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( v15_lattices @ X12 )
      | ~ ( v16_lattices @ X12 )
      | ~ ( l3_lattices @ X12 )
      | ( v15_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v15_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v16_lattices @ X12 )
      | ~ ( v15_lattices @ X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v16_lattices @ X13 )
      | ~ ( v15_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['1'])).

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

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ~ ( v11_lattices @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( v11_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v11_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v11_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v11_lattices @ X10 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v11_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v15_lattices @ X13 )
      | ~ ( v16_lattices @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( v15_lattices @ X12 )
      | ~ ( v16_lattices @ X12 )
      | ~ ( l3_lattices @ X12 )
      | ( v16_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v16_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v16_lattices @ X12 )
      | ~ ( v15_lattices @ X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v16_lattices @ X13 )
      | ~ ( v15_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(cc6_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ( v17_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc6_lattices])).

thf('8',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_A_7 )
    | ~ ( v17_lattices @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(fc2_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ~ ( v2_struct_0 @ ( k7_filter_1 @ A @ B ) )
        & ( v3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('13',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ~ ( l3_lattices @ sk_A_7 ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A_7 )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('23',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,
    ( ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf(dt_k7_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) )
        & ( l3_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( l3_lattices @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('27',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('28',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ~ ( l3_lattices @ sk_A_7 ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A_7 )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['35'])).

thf('37',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('38',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ~ ( v15_lattices @ sk_A_7 )
    | ~ ( v16_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ sk_A_7 )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','38'])).

thf('40',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v17_lattices @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v17_lattices @ sk_A_7 )
   <= ( v17_lattices @ sk_A_7 ) ),
    inference(split,[status(esa)],['43'])).

thf(cc5_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) ) ) ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( l3_lattices @ sk_A_7 )
    | ( v15_lattices @ sk_A_7 )
    | ~ ( v17_lattices @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v15_lattices @ sk_A_7 )
    | ~ ( v17_lattices @ sk_A_7 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v15_lattices @ sk_A_7 )
   <= ( v17_lattices @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( l3_lattices @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ~ ( l3_lattices @ sk_A_7 )
      | ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf(fc3_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( l3_lattices @ B ) )
     => ( ( v3_lattices @ ( k7_filter_1 @ A @ B ) )
        & ( v10_lattices @ ( k7_filter_1 @ A @ B ) ) ) ) )).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( v10_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_filter_1])).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ( v16_lattices @ X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ~ ( v10_lattices @ sk_A_7 )
      | ~ ( l3_lattices @ sk_A_7 )
      | ( v16_lattices @ sk_B )
      | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('77',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('78',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( l3_lattices @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('80',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ~ ( l3_lattices @ sk_A_7 )
      | ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ( v16_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('94',plain,
    ( ( ( v16_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v16_lattices @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v16_lattices @ sk_B )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ( v17_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc6_lattices])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v17_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v11_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v17_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v11_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ~ ( v11_lattices @ sk_B )
      | ~ ( v15_lattices @ sk_B )
      | ( v17_lattices @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('106',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( l3_lattices @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('108',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v11_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ~ ( l3_lattices @ sk_A_7 )
      | ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['120'])).

thf('122',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( v10_lattices @ ( k7_filter_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_filter_1])).

thf('123',plain,
    ( ~ ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ~ ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('124',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 )
      | ~ ( v10_lattices @ sk_A_7 )
      | ~ ( l3_lattices @ sk_A_7 ) )
   <= ~ ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ~ ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A_7 )
   <= ~ ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['133'])).

thf('135',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['121','134'])).

thf('136',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ( v11_lattices @ X10 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ sk_A_7 )
    | ( v11_lattices @ sk_B )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('141',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ( v11_lattices @ sk_B )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142'])).

thf('144',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_A_7 )
      | ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v11_lattices @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v11_lattices @ sk_B )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('152',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['121','134'])).

thf('153',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ( v15_lattices @ X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ sk_A_7 )
    | ( v15_lattices @ sk_B )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('158',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ( v15_lattices @ sk_B )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155','156','157','158','159'])).

thf('161',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','160'])).

thf('162',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('165',plain,
    ( ( ( v2_struct_0 @ sk_A_7 )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v15_lattices @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','150','169'])).

thf('171',plain,
    ( ~ ( v17_lattices @ sk_B )
   <= ~ ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('172',plain,
    ( ( v17_lattices @ sk_B )
    | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['173'])).

thf('175',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('176',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l3_lattices @ sk_A_7 )
    | ~ ( v17_lattices @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('178',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['121','134'])).

thf('179',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v17_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v17_lattices @ sk_A_7 )
    | ( v2_struct_0 @ sk_A_7 ) ),
    inference(demod,[status(thm)],['176','177','178','179','180','181','182'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_A_7 )
      | ~ ( v17_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','183'])).

thf('185',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('186',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['121','134'])).

thf('187',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ( v16_lattices @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ sk_A_7 )
    | ( v16_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('192',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ( v16_lattices @ sk_A_7 )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['188','189','190','191','192','193'])).

thf('195',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v16_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','194'])).

thf('196',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('197',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v16_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('199',plain,
    ( ( ( v2_struct_0 @ sk_A_7 )
      | ( v16_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v16_lattices @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v16_lattices @ sk_A_7 )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ( v17_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc6_lattices])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ~ ( l3_lattices @ sk_A_7 )
    | ( v17_lattices @ sk_A_7 )
    | ~ ( v16_lattices @ sk_A_7 )
    | ~ ( v15_lattices @ sk_A_7 )
    | ~ ( v11_lattices @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v17_lattices @ sk_A_7 )
    | ~ ( v16_lattices @ sk_A_7 )
    | ~ ( v15_lattices @ sk_A_7 )
    | ~ ( v11_lattices @ sk_A_7 ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( ~ ( v11_lattices @ sk_A_7 )
      | ~ ( v15_lattices @ sk_A_7 )
      | ( v17_lattices @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['203','208'])).

thf('210',plain,
    ( ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('211',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['121','134'])).

thf('212',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ( v11_lattices @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ sk_A_7 )
    | ( v11_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('217',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ( v11_lattices @ sk_A_7 )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v11_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['210','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('222',plain,
    ( ( ( v2_struct_0 @ sk_A_7 )
      | ( v11_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v11_lattices @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( v11_lattices @ sk_A_7 )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('228',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['121','134'])).

thf('229',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X13 @ X12 ) )
      | ( v15_lattices @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ sk_A_7 )
    | ( v15_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('234',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_A_7 )
    | ( v15_lattices @ sk_A_7 )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['230','231','232','233','234','235'])).

thf('237',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v15_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['227','236'])).

thf('238',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('239',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v15_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('241',plain,
    ( ( ( v2_struct_0 @ sk_A_7 )
      | ( v15_lattices @ sk_A_7 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v15_lattices @ sk_A_7 ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['241','242'])).

thf('244',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( v15_lattices @ sk_A_7 )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( v17_lattices @ sk_A_7 )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['209','226','245'])).

thf('247',plain,
    ( ( ( v2_struct_0 @ sk_A_7 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['184','246'])).

thf('248',plain,
    ( ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A_7 ) )
   <= ( ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('250',plain,
    ( ( ( v2_struct_0 @ sk_A_7 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v17_lattices @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( v17_lattices @ sk_A_7 )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['255'])).

thf('257',plain,(
    v17_lattices @ sk_A_7 ),
    inference('sat_resolution*',[status(thm)],['172','254','256'])).

thf('258',plain,(
    v15_lattices @ sk_A_7 ),
    inference(simpl_trail,[status(thm)],['50','257'])).

thf('259',plain,
    ( ( v17_lattices @ sk_A_7 )
   <= ( v17_lattices @ sk_A_7 ) ),
    inference(split,[status(esa)],['43'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ~ ( l3_lattices @ sk_A_7 )
    | ( v16_lattices @ sk_A_7 )
    | ~ ( v17_lattices @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v16_lattices @ sk_A_7 )
    | ~ ( v17_lattices @ sk_A_7 ) ),
    inference(demod,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( v16_lattices @ sk_A_7 )
   <= ( v17_lattices @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['259','264'])).

thf('266',plain,(
    v17_lattices @ sk_A_7 ),
    inference('sat_resolution*',[status(thm)],['172','254','256'])).

thf('267',plain,(
    v16_lattices @ sk_A_7 ),
    inference(simpl_trail,[status(thm)],['265','266'])).

thf('268',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['173'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v15_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v15_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['269','274'])).

thf('276',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,
    ( ( v17_lattices @ sk_B )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['276'])).

thf('278',plain,(
    v17_lattices @ sk_B ),
    inference('sat_resolution*',[status(thm)],['172','254','277'])).

thf('279',plain,(
    v15_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['275','278'])).

thf('280',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['173'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('282',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v16_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( v16_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('286',plain,
    ( ( v16_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['280','285'])).

thf('287',plain,(
    v17_lattices @ sk_B ),
    inference('sat_resolution*',[status(thm)],['172','254','277'])).

thf('288',plain,(
    v16_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['286','287'])).

thf('289',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A_7 )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','258','267','268','279','288'])).

thf('290',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ~ ( v11_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ sk_A_7 )
    | ~ ( v11_lattices @ sk_B )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_A_7 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','289'])).

thf('291',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( v17_lattices @ sk_A_7 )
   <= ( v17_lattices @ sk_A_7 ) ),
    inference(split,[status(esa)],['43'])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('296',plain,(
    ~ ( v2_struct_0 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ~ ( l3_lattices @ sk_A_7 )
    | ( v11_lattices @ sk_A_7 )
    | ~ ( v17_lattices @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( v11_lattices @ sk_A_7 )
    | ~ ( v17_lattices @ sk_A_7 ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,
    ( ( v11_lattices @ sk_A_7 )
   <= ( v17_lattices @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['294','299'])).

thf('301',plain,(
    v17_lattices @ sk_A_7 ),
    inference('sat_resolution*',[status(thm)],['172','254','256'])).

thf('302',plain,(
    v11_lattices @ sk_A_7 ),
    inference(simpl_trail,[status(thm)],['300','301'])).

thf('303',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['173'])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('306',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v11_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( v11_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['307','308'])).

thf('310',plain,
    ( ( v11_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['304','309'])).

thf('311',plain,(
    v17_lattices @ sk_B ),
    inference('sat_resolution*',[status(thm)],['172','254','277'])).

thf('312',plain,(
    v11_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['310','311'])).

thf('313',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A_7 )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_A_7 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['290','291','292','293','302','303','312'])).

thf('314',plain,
    ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_A_7 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['313'])).

thf('315',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A_7 )
    | ~ ( v10_lattices @ sk_A_7 )
    | ~ ( v15_lattices @ sk_A_7 )
    | ~ ( v16_lattices @ sk_A_7 )
    | ~ ( l3_lattices @ sk_A_7 )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A_7 )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','314'])).

thf('316',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v10_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    v15_lattices @ sk_A_7 ),
    inference(simpl_trail,[status(thm)],['50','257'])).

thf('320',plain,(
    v16_lattices @ sk_A_7 ),
    inference(simpl_trail,[status(thm)],['265','266'])).

thf('321',plain,(
    l3_lattices @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    v15_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['275','278'])).

thf('323',plain,(
    v16_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['286','287'])).

thf('324',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A_7 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A_7 )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(demod,[status(thm)],['315','316','317','318','319','320','321','322','323'])).

thf('325',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
    | ( v2_struct_0 @ sk_A_7 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['324'])).

thf('326',plain,
    ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) )
   <= ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('327',plain,(
    ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['172','254'])).

thf('328',plain,(
    ~ ( v17_lattices @ ( k7_filter_1 @ sk_A_7 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['326','327'])).

thf('329',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A_7 ) ),
    inference(clc,[status(thm)],['325','328'])).

thf('330',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    v2_struct_0 @ sk_A_7 ),
    inference(clc,[status(thm)],['329','330'])).

thf('332',plain,(
    $false ),
    inference(demod,[status(thm)],['0','331'])).


%------------------------------------------------------------------------------
