%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1452+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EicfjG8pMx

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  341 (14616 expanded)
%              Number of leaves         :   19 (3735 expanded)
%              Depth                    :   36
%              Number of atoms          : 2861 (347219 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k7_filter_1_type,type,(
    k7_filter_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ~ ( v15_lattices @ X11 )
      | ~ ( v16_lattices @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( v15_lattices @ X10 )
      | ~ ( v16_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v15_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v15_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v16_lattices @ X10 )
      | ~ ( v15_lattices @ X10 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v16_lattices @ X11 )
      | ~ ( v15_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ~ ( v11_lattices @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ~ ( v11_lattices @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ( v11_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v11_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( v11_lattices @ X8 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v11_lattices @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ~ ( v15_lattices @ X11 )
      | ~ ( v16_lattices @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( v15_lattices @ X10 )
      | ~ ( v16_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v16_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v16_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v16_lattices @ X10 )
      | ~ ( v15_lattices @ X10 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v16_lattices @ X11 )
      | ~ ( v15_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

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
    ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('13',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('23',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,
    ( ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( l3_lattices @ ( k7_filter_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('27',plain,
    ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('28',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['35'])).

thf('37',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('38',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v16_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','38'])).

thf('40',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v17_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v15_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('54',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('55',plain,
    ( ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('57',plain,
    ( ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['20'])).

thf('60',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

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

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ( v10_lattices @ ( k7_filter_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_filter_1])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ( v16_lattices @ X10 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('63',plain,(
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
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
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
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v16_lattices @ sk_B )
      | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('71',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( l3_lattices @ ( k7_filter_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_filter_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v2_struct_0 @ ( k7_filter_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_filter_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
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
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v16_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('88',plain,
    ( ( ( v16_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v16_lattices @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v16_lattices @ sk_B )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['90','91'])).

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
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v17_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v11_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v17_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v11_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ~ ( v11_lattices @ sk_B )
      | ~ ( v15_lattices @ sk_B )
      | ( v17_lattices @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

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
    inference(split,[status(esa)],['8'])).

thf('102',plain,
    ( ( ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

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
    inference('sat_resolution*',[status(thm)],['20'])).

thf('107',plain,
    ( ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['108'])).

thf('110',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ( v10_lattices @ ( k7_filter_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_filter_1])).

thf('111',plain,
    ( ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('112',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['121'])).

thf('123',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['109','122'])).

thf('124',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ( v11_lattices @ X8 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v11_lattices @ sk_B )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('129',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v11_lattices @ sk_B )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130'])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v11_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v11_lattices @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v11_lattices @ sk_B )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('140',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['109','122'])).

thf('141',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ( v15_lattices @ X10 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v15_lattices @ sk_B )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('146',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v15_lattices @ sk_B )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['142','143','144','145','146','147'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','148'])).

thf('150',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v15_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v15_lattices @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','138','157'])).

thf('159',plain,
    ( ~ ( v17_lattices @ sk_B )
   <= ~ ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('160',plain,
    ( ( v17_lattices @ sk_B )
    | ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['161'])).

thf('163',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('164',plain,
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

thf('165',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('166',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['109','122'])).

thf('167',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v17_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['164','165','166','167','168','169','170'])).

thf('172',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','171'])).

thf('173',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('174',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ~ ( l3_lattices @ X7 )
      | ( v10_lattices @ ( k7_filter_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_filter_1])).

thf('175',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ( v16_lattices @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('176',plain,(
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
      | ( v16_lattices @ X1 )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X1 @ X0 ) )
      | ( v16_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ~ ( l3_lattices @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( v16_lattices @ sk_A )
      | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','177'])).

thf('179',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('184',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v16_lattices @ sk_A )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182','183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('187',plain,
    ( ( ( v16_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v16_lattices @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v16_lattices @ sk_A )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_lattices @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ~ ( v16_lattices @ X1 )
      | ( v17_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc6_lattices])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v17_lattices @ sk_A )
    | ~ ( v16_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v17_lattices @ sk_A )
    | ~ ( v16_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ~ ( v11_lattices @ sk_A )
      | ~ ( v15_lattices @ sk_A )
      | ( v17_lattices @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['191','196'])).

thf('198',plain,
    ( ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('199',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['109','122'])).

thf('200',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( v11_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X9 @ X8 ) )
      | ( v11_lattices @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_filter_1])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v11_lattices @ sk_A )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('205',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v11_lattices @ sk_A )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['201','202','203','204','205','206'])).

thf('208',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v11_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['198','207'])).

thf('209',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('210',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v11_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v11_lattices @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['210','211'])).

thf('213',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v11_lattices @ sk_A )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('216',plain,(
    v10_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['109','122'])).

thf('217',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v10_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( v16_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ~ ( l3_lattices @ ( k7_filter_1 @ X11 @ X10 ) )
      | ( v15_lattices @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t46_filter_1])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    l3_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','36'])).

thf('222',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( v16_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['218','219','220','221','222','223'])).

thf('225',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['215','224'])).

thf('226',plain,
    ( ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('227',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v15_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('229',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v15_lattices @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v15_lattices @ sk_A ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v15_lattices @ sk_A )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( v17_lattices @ sk_A )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['197','214','233'])).

thf('235',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v17_lattices @ sk_B )
      | ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) )
   <= ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','234'])).

thf('236',plain,
    ( ( ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['162','235'])).

thf('237',plain,(
    ~ ( v2_struct_0 @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['9','21'])).

thf('238',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ( v17_lattices @ sk_B )
      & ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v17_lattices @ sk_A )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['243'])).

thf('245',plain,(
    v17_lattices @ sk_A ),
    inference('sat_resolution*',[status(thm)],['160','242','244'])).

thf('246',plain,(
    v15_lattices @ sk_A ),
    inference(simpl_trail,[status(thm)],['50','245'])).

thf('247',plain,
    ( ( v17_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v16_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v16_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,
    ( ( v16_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['247','252'])).

thf('254',plain,(
    v17_lattices @ sk_A ),
    inference('sat_resolution*',[status(thm)],['160','242','244'])).

thf('255',plain,(
    v16_lattices @ sk_A ),
    inference(simpl_trail,[status(thm)],['253','254'])).

thf('256',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['161'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v15_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('259',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v15_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v15_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('263',plain,
    ( ( v15_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['257','262'])).

thf('264',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v17_lattices @ sk_B )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['264'])).

thf('266',plain,(
    v17_lattices @ sk_B ),
    inference('sat_resolution*',[status(thm)],['160','242','265'])).

thf('267',plain,(
    v15_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['263','266'])).

thf('268',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['161'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v16_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( v16_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,
    ( ( v16_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['268','273'])).

thf('275',plain,(
    v17_lattices @ sk_B ),
    inference('sat_resolution*',[status(thm)],['160','242','265'])).

thf('276',plain,(
    v16_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v11_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','246','255','256','267','276'])).

thf('278',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_B )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','277'])).

thf('279',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( v17_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('284',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v11_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( v11_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( v11_lattices @ sk_A )
   <= ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['282','287'])).

thf('289',plain,(
    v17_lattices @ sk_A ),
    inference('sat_resolution*',[status(thm)],['160','242','244'])).

thf('290',plain,(
    v11_lattices @ sk_A ),
    inference(simpl_trail,[status(thm)],['288','289'])).

thf('291',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( v17_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference(split,[status(esa)],['161'])).

thf('293',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('294',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v11_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( v11_lattices @ sk_B )
    | ~ ( v17_lattices @ sk_B ) ),
    inference(demod,[status(thm)],['295','296'])).

thf('298',plain,
    ( ( v11_lattices @ sk_B )
   <= ( v17_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['292','297'])).

thf('299',plain,(
    v17_lattices @ sk_B ),
    inference('sat_resolution*',[status(thm)],['160','242','265'])).

thf('300',plain,(
    v11_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['298','299'])).

thf('301',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['278','279','280','281','290','291','300'])).

thf('302',plain,
    ( ~ ( v15_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A )
    | ~ ( v16_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_B )
    | ~ ( v16_lattices @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','302'])).

thf('304',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v15_lattices @ sk_A ),
    inference(simpl_trail,[status(thm)],['50','245'])).

thf('308',plain,(
    v16_lattices @ sk_A ),
    inference(simpl_trail,[status(thm)],['253','254'])).

thf('309',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    v15_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['263','266'])).

thf('311',plain,(
    v16_lattices @ sk_B ),
    inference(simpl_trail,[status(thm)],['274','275'])).

thf('312',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['303','304','305','306','307','308','309','310','311'])).

thf('313',plain,
    ( ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['312'])).

thf('314',plain,
    ( ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) )
   <= ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('315',plain,(
    ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['160','242'])).

thf('316',plain,(
    ~ ( v17_lattices @ ( k7_filter_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['314','315'])).

thf('317',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['313','316'])).

thf('318',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['317','318'])).

thf('320',plain,(
    $false ),
    inference(demod,[status(thm)],['0','319'])).


%------------------------------------------------------------------------------
