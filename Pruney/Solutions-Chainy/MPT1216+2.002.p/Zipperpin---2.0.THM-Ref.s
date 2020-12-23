%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.820Fl20ubm

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:37 EST 2020

% Result     : Theorem 6.54s
% Output     : Refutation 6.54s
% Verified   : 
% Statistics : Number of formulae       :  497 (2901 expanded)
%              Number of leaves         :   55 ( 850 expanded)
%              Depth                    :   32
%              Number of atoms          : 4820 (49046 expanded)
%              Number of equality atoms :  210 (1640 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(v16_lattices_type,type,(
    v16_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(v15_lattices_type,type,(
    v15_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(t52_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( k4_lattices @ A @ B @ C )
                  = ( k5_lattices @ A ) )
              <=> ( r3_lattices @ A @ B @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v17_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( k4_lattices @ A @ B @ C )
                    = ( k5_lattices @ A ) )
                <=> ( r3_lattices @ A @ B @ ( k7_lattices @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_lattices])).

thf('0',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    | ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != ( k5_lattices @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
   <= ~ ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    | ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != ( k5_lattices @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    | ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = ( k5_lattices @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
   <= ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_lattices @ A @ B @ C )
      <=> ( r1_lattices @ A @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l3_lattices @ X30 )
      | ~ ( v9_lattices @ X30 )
      | ~ ( v8_lattices @ X30 )
      | ~ ( v6_lattices @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( r1_lattices @ X30 @ X29 @ X31 )
      | ~ ( r3_lattices @ X30 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v6_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v8_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v9_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','13','19','25','26'])).

thf('28',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) )
   <= ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_lattices,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) )
   <= ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
   <= ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k2_lattices @ A @ B @ C )
                  = B ) ) ) ) ) )).

thf('41',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r1_lattices @ X37 @ X36 @ X38 )
      | ( ( k2_lattices @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( l3_lattices @ X37 )
      | ~ ( v9_lattices @ X37 )
      | ~ ( v8_lattices @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ X0 )
        = sk_B_2 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('44',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('45',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ X0 )
        = sk_B_2 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    | ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
      = sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
      = sk_B_2 )
    | ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
      = sk_B_2 )
   <= ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(d7_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v7_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( k2_lattices @ A @ B @ ( k2_lattices @ A @ C @ D ) )
                      = ( k2_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v7_lattices @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k2_lattices @ X11 @ X12 @ X14 ) )
        = ( k2_lattices @ X11 @ ( k2_lattices @ X11 @ X13 @ X12 ) @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_lattices])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) ) @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ) @ X1 ) )
      | ~ ( v7_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('63',plain,(
    ! [X22: $i] :
      ( ( l1_lattices @ X22 )
      | ~ ( l3_lattices @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('64',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v7_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v7_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v7_lattices @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) ) @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','64','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) )
            = B ) ) ) )).

thf('73',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( u1_struct_0 @ X70 ) )
      | ( ( k7_lattices @ X70 @ ( k7_lattices @ X70 @ X69 ) )
        = X69 )
      | ~ ( l3_lattices @ X70 )
      | ~ ( v17_lattices @ X70 )
      | ~ ( v10_lattices @ X70 )
      | ( v2_struct_0 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t49_lattices])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference(clc,[status(thm)],['78','79'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_2 @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) )
    = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['51','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ B )
            = ( k5_lattices @ A ) ) ) ) )).

thf('88',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( u1_struct_0 @ X66 ) )
      | ( ( k4_lattices @ X66 @ ( k7_lattices @ X66 @ X65 ) @ X65 )
        = ( k5_lattices @ X66 ) )
      | ~ ( l3_lattices @ X66 )
      | ~ ( v17_lattices @ X66 )
      | ~ ( v10_lattices @ X66 )
      | ( v2_struct_0 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t47_lattices])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) @ sk_C_2 )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k4_lattices @ A @ C @ B ) ) ) )).

thf('95',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k4_lattices @ X9 @ X8 @ X10 )
        = ( k4_lattices @ X9 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('98',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('104',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('105',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_lattices @ X27 )
      | ~ ( v6_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( ( k4_lattices @ X27 @ X26 @ X28 )
        = ( k2_lattices @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('108',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    = ( k2_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_2 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['102','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B )
            = ( k5_lattices @ A ) ) ) ) )).

thf('118',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( u1_struct_0 @ X60 ) )
      | ( ( k4_lattices @ X60 @ ( k5_lattices @ X60 ) @ X59 )
        = ( k5_lattices @ X60 ) )
      | ~ ( l3_lattices @ X60 )
      | ~ ( v13_lattices @ X60 )
      | ~ ( v10_lattices @ X60 )
      | ( v2_struct_0 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t40_lattices])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_2 )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v15_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v13_lattices @ A )
          & ( v14_lattices @ A ) ) ) ) )).

thf('121',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v15_lattices @ X3 )
      | ( v13_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) ) ) ) )).

thf('125',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v17_lattices @ X4 )
      | ( v15_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v15_lattices @ sk_A ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['123','124','130'])).

thf('132',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('133',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('134',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k4_lattices @ X9 @ X8 @ X10 )
        = ( k4_lattices @ X9 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('138',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
      = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['133','141'])).

thf('143',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
      = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
    = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('148',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_lattices @ X27 )
      | ~ ( v6_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( ( k4_lattices @ X27 @ X26 @ X28 )
        = ( k2_lattices @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('152',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
      = ( k2_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['147','155'])).

thf('157',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
      = ( k2_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
    = ( k2_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
    = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['146','160'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120','131','132','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k5_lattices @ sk_A ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k5_lattices @ sk_A )
    = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['86','116','164'])).

thf('166',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('167',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('170',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('176',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v7_lattices @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k2_lattices @ X11 @ X12 @ X14 ) )
        = ( k2_lattices @ X11 @ ( k2_lattices @ X11 @ X13 @ X12 ) @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_lattices])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) ) @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ) @ X1 ) )
      | ~ ( v7_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('184',plain,(
    v7_lattices @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) ) @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( u1_struct_0 @ X70 ) )
      | ( ( k7_lattices @ X70 @ ( k7_lattices @ X70 @ X69 ) )
        = X69 )
      | ~ ( l3_lattices @ X70 )
      | ~ ( v17_lattices @ X70 )
      | ~ ( v10_lattices @ X70 )
      | ( v2_struct_0 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t49_lattices])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference(clc,[status(thm)],['192','193'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_B_2 @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_2 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['185','194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['167','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('200',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('203',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('206',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['203','206'])).

thf('208',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['200','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) )
    = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['166','211'])).

thf('213',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) )
    = ( k5_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['165','212'])).

thf('214',plain,
    ( ( ( k2_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
      = ( k5_lattices @ sk_A ) )
   <= ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['50','213'])).

thf('215',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['200','207'])).

thf('216',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = ( k5_lattices @ sk_A ) )
   <= ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('218',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != ( k5_lattices @ sk_A ) )
   <= ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != ( k5_lattices @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('219',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != ( k5_lattices @ sk_A ) )
   <= ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
   <= ( ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
       != ( k5_lattices @ sk_A ) )
      & ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = ( k5_lattices @ sk_A ) )
    | ~ ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','221'])).

thf('223',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','222'])).

thf('224',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('225',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ( ( k2_lattices @ X37 @ X36 @ X38 )
       != X36 )
      | ( r1_lattices @ X37 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( l3_lattices @ X37 )
      | ~ ( v9_lattices @ X37 )
      | ~ ( v8_lattices @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ X0 )
       != sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('229',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('230',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ X0 )
       != sk_B_2 ) ) ),
    inference(demod,[status(thm)],['227','228','229','230'])).

thf('232',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
     != sk_B_2 )
    | ( r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['224','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    | ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
     != sk_B_2 ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf(t51_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) )
                = ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf('237',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( u1_struct_0 @ X75 ) )
      | ( ( k7_lattices @ X75 @ ( k3_lattices @ X75 @ X74 @ X76 ) )
        = ( k4_lattices @ X75 @ ( k7_lattices @ X75 @ X74 ) @ ( k7_lattices @ X75 @ X76 ) ) )
      | ~ ( m1_subset_1 @ X76 @ ( u1_struct_0 @ X75 ) )
      | ~ ( l3_lattices @ X75 )
      | ~ ( v17_lattices @ X75 )
      | ~ ( v10_lattices @ X75 )
      | ( v2_struct_0 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t51_lattices])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference(clc,[status(thm)],['192','193'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X0 ) )
        = ( k4_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['238','239','240','241','242'])).

thf('244',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X0 ) )
        = ( k4_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_C_2 ) )
    = ( k4_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['235','245'])).

thf('247',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('248',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k3_lattices @ A @ C @ B ) ) ) )).

thf('249',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k3_lattices @ X6 @ X5 @ X7 )
        = ( k3_lattices @ X6 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v4_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('252',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    ! [X22: $i] :
      ( ( l2_lattices @ X22 )
      | ~ ( l3_lattices @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('259',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['250','256','259'])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('263',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['247','262'])).

thf('264',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('265',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('266',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l2_lattices @ X24 )
      | ~ ( v4_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( ( k3_lattices @ X24 @ X23 @ X25 )
        = ( k1_lattices @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('269',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['257','258'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['267','268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['264','272'])).

thf('274',plain,
    ( ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['263','273'])).

thf('275',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('277',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    = ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( k7_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) ) )
    = ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['246','274','277'])).

thf('279',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf(t31_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v11_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( k3_lattices @ A @ B @ ( k4_lattices @ A @ C @ D ) )
                    = ( k4_lattices @ A @ ( k3_lattices @ A @ B @ C ) @ ( k3_lattices @ A @ B @ D ) ) ) ) ) ) ) )).

thf('282',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ X50 ) )
      | ( ( k3_lattices @ X50 @ X49 @ ( k4_lattices @ X50 @ X52 @ X51 ) )
        = ( k4_lattices @ X50 @ ( k3_lattices @ X50 @ X49 @ X52 ) @ ( k3_lattices @ X50 @ X49 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ X50 ) )
      | ~ ( l3_lattices @ X50 )
      | ~ ( v11_lattices @ X50 )
      | ~ ( v10_lattices @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_lattices])).

thf('283',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k4_lattices @ sk_A @ X0 @ X1 ) )
        = ( k4_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X0 ) @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v17_lattices @ X4 )
      | ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('286',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v11_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    v11_lattices @ sk_A ),
    inference(demod,[status(thm)],['287','288','289'])).

thf('291',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k4_lattices @ sk_A @ X0 @ X1 ) )
        = ( k4_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X0 ) @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['283','284','290','291'])).

thf('293',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['280','292'])).

thf('294',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('295',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k3_lattices @ X6 @ X5 @ X7 )
        = ( k3_lattices @ X6 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('297',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('299',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['257','258'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['297','298','299'])).

thf('301',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['300','301'])).

thf('303',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['294','302'])).

thf('304',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('305',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l2_lattices @ X24 )
      | ~ ( v4_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( ( k3_lattices @ X24 @ X23 @ X25 )
        = ( k1_lattices @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('309',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['257','258'])).

thf('310',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['307','308','309'])).

thf('311',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['310','311'])).

thf('313',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['304','312'])).

thf('314',plain,
    ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['303','313'])).

thf('315',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ B )
            = ( k6_lattices @ A ) ) ) ) )).

thf('316',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( u1_struct_0 @ X68 ) )
      | ( ( k3_lattices @ X68 @ ( k7_lattices @ X68 @ X67 ) @ X67 )
        = ( k6_lattices @ X68 ) )
      | ~ ( l3_lattices @ X68 )
      | ~ ( v17_lattices @ X68 )
      | ~ ( v10_lattices @ X68 )
      | ( v2_struct_0 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t48_lattices])).

thf('317',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_B_2 )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['315','316'])).

thf('318',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['303','313'])).

thf('322',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['317','318','319','320','321'])).

thf('323',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,
    ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['322','323'])).

thf('325',plain,
    ( ( k6_lattices @ sk_A )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['314','324'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['293','325'])).

thf('327',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['326','327'])).

thf('329',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['279','328'])).

thf('330',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = ( k5_lattices @ sk_A ) )
   <= ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = ( k5_lattices @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('331',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = ( k5_lattices @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('332',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k5_lattices @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','221','331'])).

thf('333',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k5_lattices @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['330','332'])).

thf('334',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('335',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('336',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k3_lattices @ X6 @ X5 @ X7 )
        = ( k3_lattices @ X6 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('337',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k3_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['335','336'])).

thf('338',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k3_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['337'])).

thf('339',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k5_lattices @ sk_A ) ) )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['334','338'])).

thf('340',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('341',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('342',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['257','258'])).

thf('343',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k5_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['339','340','341','342'])).

thf('344',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,
    ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k5_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['343','344'])).

thf('346',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf(t39_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B )
            = B ) ) ) )).

thf('347',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ X58 ) )
      | ( ( k3_lattices @ X58 @ ( k5_lattices @ X58 ) @ X57 )
        = X57 )
      | ~ ( l3_lattices @ X58 )
      | ~ ( v13_lattices @ X58 )
      | ~ ( v10_lattices @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t39_lattices])).

thf('348',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = ( k7_lattices @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['346','347'])).

thf('349',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['123','124','130'])).

thf('351',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = ( k7_lattices @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['348','349','350','351'])).

thf('353',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,
    ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k7_lattices @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['352','353'])).

thf('355',plain,
    ( ( k7_lattices @ sk_A @ sk_B_2 )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['345','354'])).

thf('356',plain,
    ( ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['263','273'])).

thf('357',plain,
    ( ( k7_lattices @ sk_A @ sk_B_2 )
    = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['329','333','355','356'])).

thf('358',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf(dt_k6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('359',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l2_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('360',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ X50 ) )
      | ( ( k3_lattices @ X50 @ X49 @ ( k4_lattices @ X50 @ X52 @ X51 ) )
        = ( k4_lattices @ X50 @ ( k3_lattices @ X50 @ X49 @ X52 ) @ ( k3_lattices @ X50 @ X49 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ X50 ) )
      | ~ ( l3_lattices @ X50 )
      | ~ ( v11_lattices @ X50 )
      | ~ ( v10_lattices @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_lattices])).

thf('362',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k4_lattices @ sk_A @ X0 @ X1 ) )
        = ( k4_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C_2 @ X0 ) @ ( k3_lattices @ sk_A @ sk_C_2 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['360','361'])).

thf('363',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('364',plain,(
    v11_lattices @ sk_A ),
    inference(demod,[status(thm)],['287','288','289'])).

thf('365',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k4_lattices @ sk_A @ X0 @ X1 ) )
        = ( k4_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C_2 @ X0 ) @ ( k3_lattices @ sk_A @ sk_C_2 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['362','363','364','365'])).

thf('367',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) @ ( k3_lattices @ sk_A @ sk_C_2 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['359','366'])).

thf('368',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['257','258'])).

thf('369',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l2_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('370',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('371',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['369','370'])).

thf('372',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['257','258'])).

thf('373',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['371','372'])).

thf('374',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) )
    = ( k1_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['373','374'])).

thf('376',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B )
            = ( k6_lattices @ A ) ) ) ) )).

thf('377',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( u1_struct_0 @ X64 ) )
      | ( ( k3_lattices @ X64 @ ( k6_lattices @ X64 ) @ X63 )
        = ( k6_lattices @ X64 ) )
      | ~ ( l3_lattices @ X64 )
      | ~ ( v14_lattices @ X64 )
      | ~ ( v10_lattices @ X64 )
      | ( v2_struct_0 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t44_lattices])).

thf('378',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_C_2 )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['376','377'])).

thf('379',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('380',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v15_lattices @ X3 )
      | ( v14_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('381',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v14_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['380','381'])).

thf('383',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,(
    v15_lattices @ sk_A ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('385',plain,(
    v14_lattices @ sk_A ),
    inference(demod,[status(thm)],['382','383','384'])).

thf('386',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('388',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l2_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('389',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k3_lattices @ X6 @ X5 @ X7 )
        = ( k3_lattices @ X6 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('390',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 )
        = ( k3_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['388','389'])).

thf('391',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 )
        = ( k3_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['390'])).

thf('392',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_C_2 )
      = ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) )
    | ~ ( v4_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['387','391'])).

thf('393',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['257','258'])).

thf('394',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('395',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_C_2 )
      = ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['392','393','394'])).

thf('396',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_C_2 )
    = ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['395','396'])).

thf('398',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) )
    = ( k1_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['373','374'])).

thf('399',plain,
    ( ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_C_2 )
    = ( k1_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['397','398'])).

thf('400',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['378','379','385','386','399'])).

thf('401',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,
    ( ( k1_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['400','401'])).

thf('403',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['375','402'])).

thf('404',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k3_lattices @ sk_A @ sk_C_2 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['367','368','403'])).

thf('405',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k3_lattices @ sk_A @ sk_C_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['404'])).

thf('406',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k3_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['405','406'])).

thf('408',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) ) )
    = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k3_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['358','407'])).

thf('409',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf(t43_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B )
            = B ) ) ) )).

thf('410',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ X62 ) )
      | ( ( k4_lattices @ X62 @ ( k6_lattices @ X62 ) @ X61 )
        = X61 )
      | ~ ( l3_lattices @ X62 )
      | ~ ( v14_lattices @ X62 )
      | ~ ( v10_lattices @ X62 )
      | ( v2_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t43_lattices])).

thf('411',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = ( k7_lattices @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['409','410'])).

thf('412',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('413',plain,(
    v14_lattices @ sk_A ),
    inference(demod,[status(thm)],['382','383','384'])).

thf('414',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('415',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
      = ( k7_lattices @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['411','412','413','414'])).

thf('416',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('417',plain,
    ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k7_lattices @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['415','416'])).

thf('418',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['264','272'])).

thf('419',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['264','272'])).

thf('420',plain,
    ( ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['408','417','418','419'])).

thf('421',plain,
    ( ( k1_lattices @ sk_A @ sk_C_2 @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k7_lattices @ sk_A @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['357','420'])).

thf('422',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['278','421'])).

thf('423',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference(clc,[status(thm)],['192','193'])).

thf('424',plain,
    ( sk_B_2
    = ( k2_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['422','423'])).

thf('425',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) )
    | ( sk_B_2 != sk_B_2 ) ),
    inference(demod,[status(thm)],['234','424'])).

thf('426',plain,(
    r1_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['425'])).

thf('427',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('428',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l3_lattices @ X30 )
      | ~ ( v9_lattices @ X30 )
      | ~ ( v8_lattices @ X30 )
      | ~ ( v6_lattices @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( r3_lattices @ X30 @ X29 @ X31 )
      | ~ ( r1_lattices @ X30 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('429',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['427','428'])).

thf('430',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('431',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('432',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('433',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['429','430','431','432','433'])).

thf('435',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['426','434'])).

thf('436',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('437',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['435','436'])).

thf('438',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('439',plain,(
    r3_lattices @ sk_A @ sk_B_2 @ ( k7_lattices @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['437','438'])).

thf('440',plain,(
    $false ),
    inference(demod,[status(thm)],['223','439'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.820Fl20ubm
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.54/6.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.54/6.70  % Solved by: fo/fo7.sh
% 6.54/6.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.54/6.70  % done 5896 iterations in 6.221s
% 6.54/6.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.54/6.70  % SZS output start Refutation
% 6.54/6.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.54/6.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.54/6.70  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 6.54/6.70  thf(sk_C_2_type, type, sk_C_2: $i).
% 6.54/6.70  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 6.54/6.70  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 6.54/6.70  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 6.54/6.70  thf(v16_lattices_type, type, v16_lattices: $i > $o).
% 6.54/6.70  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 6.54/6.70  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 6.54/6.70  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 6.54/6.70  thf(sk_B_2_type, type, sk_B_2: $i).
% 6.54/6.70  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 6.54/6.70  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 6.54/6.70  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 6.54/6.70  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 6.54/6.70  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 6.54/6.70  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 6.54/6.70  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 6.54/6.70  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 6.54/6.70  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 6.54/6.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.54/6.70  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 6.54/6.70  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 6.54/6.70  thf(sk_A_type, type, sk_A: $i).
% 6.54/6.70  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 6.54/6.70  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 6.54/6.70  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 6.54/6.70  thf(v15_lattices_type, type, v15_lattices: $i > $o).
% 6.54/6.70  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 6.54/6.70  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 6.54/6.70  thf(t52_lattices, conjecture,
% 6.54/6.70    (![A:$i]:
% 6.54/6.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.70         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.70       ( ![B:$i]:
% 6.54/6.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.70           ( ![C:$i]:
% 6.54/6.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.70               ( ( ( k4_lattices @ A @ B @ C ) = ( k5_lattices @ A ) ) <=>
% 6.54/6.70                 ( r3_lattices @ A @ B @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 6.54/6.70  thf(zf_stmt_0, negated_conjecture,
% 6.54/6.70    (~( ![A:$i]:
% 6.54/6.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.70            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.70          ( ![B:$i]:
% 6.54/6.70            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.70              ( ![C:$i]:
% 6.54/6.70                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.70                  ( ( ( k4_lattices @ A @ B @ C ) = ( k5_lattices @ A ) ) <=>
% 6.54/6.70                    ( r3_lattices @ A @ B @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ) )),
% 6.54/6.70    inference('cnf.neg', [status(esa)], [t52_lattices])).
% 6.54/6.70  thf('0', plain,
% 6.54/6.70      ((~ (r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.70        | ((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) != (k5_lattices @ sk_A)))),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('1', plain,
% 6.54/6.70      ((~ (r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))
% 6.54/6.70         <= (~ ((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.70      inference('split', [status(esa)], ['0'])).
% 6.54/6.70  thf('2', plain,
% 6.54/6.70      (~ ((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))) | 
% 6.54/6.70       ~ (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A)))),
% 6.54/6.70      inference('split', [status(esa)], ['0'])).
% 6.54/6.70  thf('3', plain,
% 6.54/6.70      (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.70        | ((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A)))),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('4', plain,
% 6.54/6.70      (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))
% 6.54/6.70         <= (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.70      inference('split', [status(esa)], ['3'])).
% 6.54/6.70  thf('5', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf(redefinition_r3_lattices, axiom,
% 6.54/6.70    (![A:$i,B:$i,C:$i]:
% 6.54/6.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 6.54/6.70         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 6.54/6.70         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 6.54/6.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 6.54/6.70       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 6.54/6.70  thf('6', plain,
% 6.54/6.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.54/6.70         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 6.54/6.70          | ~ (l3_lattices @ X30)
% 6.54/6.70          | ~ (v9_lattices @ X30)
% 6.54/6.70          | ~ (v8_lattices @ X30)
% 6.54/6.70          | ~ (v6_lattices @ X30)
% 6.54/6.70          | (v2_struct_0 @ X30)
% 6.54/6.70          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 6.54/6.70          | (r1_lattices @ X30 @ X29 @ X31)
% 6.54/6.70          | ~ (r3_lattices @ X30 @ X29 @ X31))),
% 6.54/6.70      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 6.54/6.70  thf('7', plain,
% 6.54/6.70      (![X0 : $i]:
% 6.54/6.70         (~ (r3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.70          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.70          | (v2_struct_0 @ sk_A)
% 6.54/6.70          | ~ (v6_lattices @ sk_A)
% 6.54/6.70          | ~ (v8_lattices @ sk_A)
% 6.54/6.70          | ~ (v9_lattices @ sk_A)
% 6.54/6.70          | ~ (l3_lattices @ sk_A))),
% 6.54/6.70      inference('sup-', [status(thm)], ['5', '6'])).
% 6.54/6.70  thf(cc1_lattices, axiom,
% 6.54/6.70    (![A:$i]:
% 6.54/6.70     ( ( l3_lattices @ A ) =>
% 6.54/6.70       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 6.54/6.70         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 6.54/6.70           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 6.54/6.70           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 6.54/6.70  thf('8', plain,
% 6.54/6.70      (![X2 : $i]:
% 6.54/6.70         ((v2_struct_0 @ X2)
% 6.54/6.70          | ~ (v10_lattices @ X2)
% 6.54/6.70          | (v6_lattices @ X2)
% 6.54/6.70          | ~ (l3_lattices @ X2))),
% 6.54/6.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.54/6.70  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('10', plain,
% 6.54/6.70      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.54/6.70      inference('sup-', [status(thm)], ['8', '9'])).
% 6.54/6.70  thf('11', plain, ((l3_lattices @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('12', plain, ((v10_lattices @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('13', plain, ((v6_lattices @ sk_A)),
% 6.54/6.70      inference('demod', [status(thm)], ['10', '11', '12'])).
% 6.54/6.70  thf('14', plain,
% 6.54/6.70      (![X2 : $i]:
% 6.54/6.70         ((v2_struct_0 @ X2)
% 6.54/6.70          | ~ (v10_lattices @ X2)
% 6.54/6.70          | (v8_lattices @ X2)
% 6.54/6.70          | ~ (l3_lattices @ X2))),
% 6.54/6.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.54/6.70  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('16', plain,
% 6.54/6.70      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.54/6.70      inference('sup-', [status(thm)], ['14', '15'])).
% 6.54/6.70  thf('17', plain, ((l3_lattices @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('18', plain, ((v10_lattices @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('19', plain, ((v8_lattices @ sk_A)),
% 6.54/6.70      inference('demod', [status(thm)], ['16', '17', '18'])).
% 6.54/6.70  thf('20', plain,
% 6.54/6.70      (![X2 : $i]:
% 6.54/6.70         ((v2_struct_0 @ X2)
% 6.54/6.70          | ~ (v10_lattices @ X2)
% 6.54/6.70          | (v9_lattices @ X2)
% 6.54/6.70          | ~ (l3_lattices @ X2))),
% 6.54/6.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.54/6.70  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('22', plain,
% 6.54/6.70      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.54/6.70      inference('sup-', [status(thm)], ['20', '21'])).
% 6.54/6.70  thf('23', plain, ((l3_lattices @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('24', plain, ((v10_lattices @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('25', plain, ((v9_lattices @ sk_A)),
% 6.54/6.70      inference('demod', [status(thm)], ['22', '23', '24'])).
% 6.54/6.70  thf('26', plain, ((l3_lattices @ sk_A)),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf('27', plain,
% 6.54/6.70      (![X0 : $i]:
% 6.54/6.70         (~ (r3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.70          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.70          | (v2_struct_0 @ sk_A))),
% 6.54/6.70      inference('demod', [status(thm)], ['7', '13', '19', '25', '26'])).
% 6.54/6.70  thf('28', plain,
% 6.54/6.70      ((((v2_struct_0 @ sk_A)
% 6.54/6.70         | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ 
% 6.54/6.70              (u1_struct_0 @ sk_A))
% 6.54/6.70         | (r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))
% 6.54/6.70         <= (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.70      inference('sup-', [status(thm)], ['4', '27'])).
% 6.54/6.70  thf('29', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.70  thf(dt_k7_lattices, axiom,
% 6.54/6.70    (![A:$i,B:$i]:
% 6.54/6.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 6.54/6.70         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 6.54/6.70       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 6.54/6.70  thf('30', plain,
% 6.54/6.70      (![X20 : $i, X21 : $i]:
% 6.54/6.70         (~ (l3_lattices @ X20)
% 6.54/6.70          | (v2_struct_0 @ X20)
% 6.54/6.70          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 6.54/6.70          | (m1_subset_1 @ (k7_lattices @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 6.54/6.70      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 6.54/6.71  thf('31', plain,
% 6.54/6.71      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 6.54/6.71        | (v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['29', '30'])).
% 6.54/6.71  thf('32', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('33', plain,
% 6.54/6.71      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 6.54/6.71        | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['31', '32'])).
% 6.54/6.71  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('35', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('36', plain,
% 6.54/6.71      ((((v2_struct_0 @ sk_A)
% 6.54/6.71         | (r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))
% 6.54/6.71         <= (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.71      inference('demod', [status(thm)], ['28', '35'])).
% 6.54/6.71  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('38', plain,
% 6.54/6.71      (((r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))
% 6.54/6.71         <= (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.71      inference('clc', [status(thm)], ['36', '37'])).
% 6.54/6.71  thf('39', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('40', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(t21_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 6.54/6.71         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ![C:$i]:
% 6.54/6.71             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71               ( ( r1_lattices @ A @ B @ C ) <=>
% 6.54/6.71                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 6.54/6.71  thf('41', plain,
% 6.54/6.71      (![X36 : $i, X37 : $i, X38 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 6.54/6.71          | ~ (r1_lattices @ X37 @ X36 @ X38)
% 6.54/6.71          | ((k2_lattices @ X37 @ X36 @ X38) = (X36))
% 6.54/6.71          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 6.54/6.71          | ~ (l3_lattices @ X37)
% 6.54/6.71          | ~ (v9_lattices @ X37)
% 6.54/6.71          | ~ (v8_lattices @ X37)
% 6.54/6.71          | (v2_struct_0 @ X37))),
% 6.54/6.71      inference('cnf', [status(esa)], [t21_lattices])).
% 6.54/6.71  thf('42', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v8_lattices @ sk_A)
% 6.54/6.71          | ~ (v9_lattices @ sk_A)
% 6.54/6.71          | ~ (l3_lattices @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ sk_B_2 @ X0) = (sk_B_2))
% 6.54/6.71          | ~ (r1_lattices @ sk_A @ sk_B_2 @ X0))),
% 6.54/6.71      inference('sup-', [status(thm)], ['40', '41'])).
% 6.54/6.71  thf('43', plain, ((v8_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['16', '17', '18'])).
% 6.54/6.71  thf('44', plain, ((v9_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['22', '23', '24'])).
% 6.54/6.71  thf('45', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('46', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ sk_B_2 @ X0) = (sk_B_2))
% 6.54/6.71          | ~ (r1_lattices @ sk_A @ sk_B_2 @ X0))),
% 6.54/6.71      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 6.54/6.71  thf('47', plain,
% 6.54/6.71      ((~ (r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71        | ((k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71            = (sk_B_2))
% 6.54/6.71        | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['39', '46'])).
% 6.54/6.71  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('49', plain,
% 6.54/6.71      ((((k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71          = (sk_B_2))
% 6.54/6.71        | ~ (r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('clc', [status(thm)], ['47', '48'])).
% 6.54/6.71  thf('50', plain,
% 6.54/6.71      ((((k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71          = (sk_B_2)))
% 6.54/6.71         <= (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.71      inference('sup-', [status(thm)], ['38', '49'])).
% 6.54/6.71  thf('51', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('52', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('53', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('54', plain,
% 6.54/6.71      (![X20 : $i, X21 : $i]:
% 6.54/6.71         (~ (l3_lattices @ X20)
% 6.54/6.71          | (v2_struct_0 @ X20)
% 6.54/6.71          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 6.54/6.71          | (m1_subset_1 @ (k7_lattices @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 6.54/6.71  thf('55', plain,
% 6.54/6.71      (((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) @ 
% 6.54/6.71         (u1_struct_0 @ sk_A))
% 6.54/6.71        | (v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['53', '54'])).
% 6.54/6.71  thf('56', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('57', plain,
% 6.54/6.71      (((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) @ 
% 6.54/6.71         (u1_struct_0 @ sk_A))
% 6.54/6.71        | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['55', '56'])).
% 6.54/6.71  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('59', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) @ 
% 6.54/6.71        (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['57', '58'])).
% 6.54/6.71  thf(d7_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 6.54/6.71       ( ( v7_lattices @ A ) <=>
% 6.54/6.71         ( ![B:$i]:
% 6.54/6.71           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71             ( ![C:$i]:
% 6.54/6.71               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71                 ( ![D:$i]:
% 6.54/6.71                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71                     ( ( k2_lattices @ A @ B @ ( k2_lattices @ A @ C @ D ) ) =
% 6.54/6.71                       ( k2_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 6.54/6.71  thf('60', plain,
% 6.54/6.71      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 6.54/6.71         (~ (v7_lattices @ X11)
% 6.54/6.71          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 6.54/6.71          | ((k2_lattices @ X11 @ X13 @ (k2_lattices @ X11 @ X12 @ X14))
% 6.54/6.71              = (k2_lattices @ X11 @ (k2_lattices @ X11 @ X13 @ X12) @ X14))
% 6.54/6.71          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 6.54/6.71          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 6.54/6.71          | ~ (l1_lattices @ X11)
% 6.54/6.71          | (v2_struct_0 @ X11))),
% 6.54/6.71      inference('cnf', [status(esa)], [d7_lattices])).
% 6.54/6.71  thf('61', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (l1_lattices @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ X0 @ 
% 6.54/6.71              (k2_lattices @ sk_A @ 
% 6.54/6.71               (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) @ X1))
% 6.54/6.71              = (k2_lattices @ sk_A @ 
% 6.54/6.71                 (k2_lattices @ sk_A @ X0 @ 
% 6.54/6.71                  (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2))) @ 
% 6.54/6.71                 X1))
% 6.54/6.71          | ~ (v7_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['59', '60'])).
% 6.54/6.71  thf('62', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(dt_l3_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 6.54/6.71  thf('63', plain,
% 6.54/6.71      (![X22 : $i]: ((l1_lattices @ X22) | ~ (l3_lattices @ X22))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 6.54/6.71  thf('64', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('65', plain,
% 6.54/6.71      (![X2 : $i]:
% 6.54/6.71         ((v2_struct_0 @ X2)
% 6.54/6.71          | ~ (v10_lattices @ X2)
% 6.54/6.71          | (v7_lattices @ X2)
% 6.54/6.71          | ~ (l3_lattices @ X2))),
% 6.54/6.71      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.54/6.71  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('67', plain,
% 6.54/6.71      ((~ (l3_lattices @ sk_A) | (v7_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['65', '66'])).
% 6.54/6.71  thf('68', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('69', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('70', plain, ((v7_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['67', '68', '69'])).
% 6.54/6.71  thf('71', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ X0 @ 
% 6.54/6.71              (k2_lattices @ sk_A @ 
% 6.54/6.71               (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) @ X1))
% 6.54/6.71              = (k2_lattices @ sk_A @ 
% 6.54/6.71                 (k2_lattices @ sk_A @ X0 @ 
% 6.54/6.71                  (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2))) @ 
% 6.54/6.71                 X1)))),
% 6.54/6.71      inference('demod', [status(thm)], ['61', '64', '70'])).
% 6.54/6.71  thf('72', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(t49_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) ) = ( B ) ) ) ) ))).
% 6.54/6.71  thf('73', plain,
% 6.54/6.71      (![X69 : $i, X70 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X69 @ (u1_struct_0 @ X70))
% 6.54/6.71          | ((k7_lattices @ X70 @ (k7_lattices @ X70 @ X69)) = (X69))
% 6.54/6.71          | ~ (l3_lattices @ X70)
% 6.54/6.71          | ~ (v17_lattices @ X70)
% 6.54/6.71          | ~ (v10_lattices @ X70)
% 6.54/6.71          | (v2_struct_0 @ X70))),
% 6.54/6.71      inference('cnf', [status(esa)], [t49_lattices])).
% 6.54/6.71  thf('74', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (v10_lattices @ sk_A)
% 6.54/6.71        | ~ (v17_lattices @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A)
% 6.54/6.71        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) = (sk_C_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['72', '73'])).
% 6.54/6.71  thf('75', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('76', plain, ((v17_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('77', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('78', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) = (sk_C_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 6.54/6.71  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('80', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) = (sk_C_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['78', '79'])).
% 6.54/6.71  thf('81', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2)) = (sk_C_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['78', '79'])).
% 6.54/6.71  thf('82', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_2 @ X1))
% 6.54/6.71              = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_2) @ X1)))),
% 6.54/6.71      inference('demod', [status(thm)], ['71', '80', '81'])).
% 6.54/6.71  thf('83', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 6.54/6.71            = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['52', '82'])).
% 6.54/6.71  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('85', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 6.54/6.71              = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ 
% 6.54/6.71                 X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['83', '84'])).
% 6.54/6.71  thf('86', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_B_2 @ 
% 6.54/6.71         (k2_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_C_2)))
% 6.54/6.71         = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['51', '85'])).
% 6.54/6.71  thf('87', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(t47_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ B ) =
% 6.54/6.71             ( k5_lattices @ A ) ) ) ) ))).
% 6.54/6.71  thf('88', plain,
% 6.54/6.71      (![X65 : $i, X66 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X65 @ (u1_struct_0 @ X66))
% 6.54/6.71          | ((k4_lattices @ X66 @ (k7_lattices @ X66 @ X65) @ X65)
% 6.54/6.71              = (k5_lattices @ X66))
% 6.54/6.71          | ~ (l3_lattices @ X66)
% 6.54/6.71          | ~ (v17_lattices @ X66)
% 6.54/6.71          | ~ (v10_lattices @ X66)
% 6.54/6.71          | (v2_struct_0 @ X66))),
% 6.54/6.71      inference('cnf', [status(esa)], [t47_lattices])).
% 6.54/6.71  thf('89', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (v10_lattices @ sk_A)
% 6.54/6.71        | ~ (v17_lattices @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A)
% 6.54/6.71        | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2) @ sk_C_2)
% 6.54/6.71            = (k5_lattices @ sk_A)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['87', '88'])).
% 6.54/6.71  thf('90', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('91', plain, ((v17_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('92', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('93', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('94', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(commutativity_k4_lattices, axiom,
% 6.54/6.71    (![A:$i,B:$i,C:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 6.54/6.71         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 6.54/6.71         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 6.54/6.71       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 6.54/6.71  thf('95', plain,
% 6.54/6.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 6.54/6.71          | ~ (l1_lattices @ X9)
% 6.54/6.71          | ~ (v6_lattices @ X9)
% 6.54/6.71          | (v2_struct_0 @ X9)
% 6.54/6.71          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 6.54/6.71          | ((k4_lattices @ X9 @ X8 @ X10) = (k4_lattices @ X9 @ X10 @ X8)))),
% 6.54/6.71      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 6.54/6.71  thf('96', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71            = (k4_lattices @ sk_A @ X0 @ sk_C_2))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v6_lattices @ sk_A)
% 6.54/6.71          | ~ (l1_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['94', '95'])).
% 6.54/6.71  thf('97', plain, ((v6_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['10', '11', '12'])).
% 6.54/6.71  thf('98', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('99', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71            = (k4_lattices @ sk_A @ X0 @ sk_C_2))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['96', '97', '98'])).
% 6.54/6.71  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('101', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71              = (k4_lattices @ sk_A @ X0 @ sk_C_2)))),
% 6.54/6.71      inference('clc', [status(thm)], ['99', '100'])).
% 6.54/6.71  thf('102', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2) @ sk_C_2))),
% 6.54/6.71      inference('sup-', [status(thm)], ['93', '101'])).
% 6.54/6.71  thf('103', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('104', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(redefinition_k4_lattices, axiom,
% 6.54/6.71    (![A:$i,B:$i,C:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 6.54/6.71         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 6.54/6.71         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 6.54/6.71       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 6.54/6.71  thf('105', plain,
% 6.54/6.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 6.54/6.71          | ~ (l1_lattices @ X27)
% 6.54/6.71          | ~ (v6_lattices @ X27)
% 6.54/6.71          | (v2_struct_0 @ X27)
% 6.54/6.71          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 6.54/6.71          | ((k4_lattices @ X27 @ X26 @ X28) = (k2_lattices @ X27 @ X26 @ X28)))),
% 6.54/6.71      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 6.54/6.71  thf('106', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71            = (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v6_lattices @ sk_A)
% 6.54/6.71          | ~ (l1_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['104', '105'])).
% 6.54/6.71  thf('107', plain, ((v6_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['10', '11', '12'])).
% 6.54/6.71  thf('108', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('109', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71            = (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['106', '107', '108'])).
% 6.54/6.71  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('111', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71              = (k2_lattices @ sk_A @ sk_C_2 @ X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['109', '110'])).
% 6.54/6.71  thf('112', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['103', '111'])).
% 6.54/6.71  thf('113', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_2) @ sk_C_2))),
% 6.54/6.71      inference('demod', [status(thm)], ['102', '112'])).
% 6.54/6.71  thf('114', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k2_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71            = (k5_lattices @ sk_A)))),
% 6.54/6.71      inference('demod', [status(thm)], ['89', '90', '91', '92', '113'])).
% 6.54/6.71  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('116', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71         = (k5_lattices @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['114', '115'])).
% 6.54/6.71  thf('117', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(t40_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B ) =
% 6.54/6.71             ( k5_lattices @ A ) ) ) ) ))).
% 6.54/6.71  thf('118', plain,
% 6.54/6.71      (![X59 : $i, X60 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X59 @ (u1_struct_0 @ X60))
% 6.54/6.71          | ((k4_lattices @ X60 @ (k5_lattices @ X60) @ X59)
% 6.54/6.71              = (k5_lattices @ X60))
% 6.54/6.71          | ~ (l3_lattices @ X60)
% 6.54/6.71          | ~ (v13_lattices @ X60)
% 6.54/6.71          | ~ (v10_lattices @ X60)
% 6.54/6.71          | (v2_struct_0 @ X60))),
% 6.54/6.71      inference('cnf', [status(esa)], [t40_lattices])).
% 6.54/6.71  thf('119', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (v10_lattices @ sk_A)
% 6.54/6.71        | ~ (v13_lattices @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A)
% 6.54/6.71        | ((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_2)
% 6.54/6.71            = (k5_lattices @ sk_A)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['117', '118'])).
% 6.54/6.71  thf('120', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(cc4_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( l3_lattices @ A ) =>
% 6.54/6.71       ( ( ( ~( v2_struct_0 @ A ) ) & ( v15_lattices @ A ) ) =>
% 6.54/6.71         ( ( ~( v2_struct_0 @ A ) ) & ( v13_lattices @ A ) & 
% 6.54/6.71           ( v14_lattices @ A ) ) ) ))).
% 6.54/6.71  thf('121', plain,
% 6.54/6.71      (![X3 : $i]:
% 6.54/6.71         ((v2_struct_0 @ X3)
% 6.54/6.71          | ~ (v15_lattices @ X3)
% 6.54/6.71          | (v13_lattices @ X3)
% 6.54/6.71          | ~ (l3_lattices @ X3))),
% 6.54/6.71      inference('cnf', [status(esa)], [cc4_lattices])).
% 6.54/6.71  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('123', plain,
% 6.54/6.71      ((~ (l3_lattices @ sk_A)
% 6.54/6.71        | (v13_lattices @ sk_A)
% 6.54/6.71        | ~ (v15_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['121', '122'])).
% 6.54/6.71  thf('124', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(cc5_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( l3_lattices @ A ) =>
% 6.54/6.71       ( ( ( ~( v2_struct_0 @ A ) ) & ( v17_lattices @ A ) ) =>
% 6.54/6.71         ( ( ~( v2_struct_0 @ A ) ) & ( v11_lattices @ A ) & 
% 6.54/6.71           ( v15_lattices @ A ) & ( v16_lattices @ A ) ) ) ))).
% 6.54/6.71  thf('125', plain,
% 6.54/6.71      (![X4 : $i]:
% 6.54/6.71         ((v2_struct_0 @ X4)
% 6.54/6.71          | ~ (v17_lattices @ X4)
% 6.54/6.71          | (v15_lattices @ X4)
% 6.54/6.71          | ~ (l3_lattices @ X4))),
% 6.54/6.71      inference('cnf', [status(esa)], [cc5_lattices])).
% 6.54/6.71  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('127', plain,
% 6.54/6.71      ((~ (l3_lattices @ sk_A)
% 6.54/6.71        | (v15_lattices @ sk_A)
% 6.54/6.71        | ~ (v17_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['125', '126'])).
% 6.54/6.71  thf('128', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('129', plain, ((v17_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('130', plain, ((v15_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['127', '128', '129'])).
% 6.54/6.71  thf('131', plain, ((v13_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['123', '124', '130'])).
% 6.54/6.71  thf('132', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(dt_k5_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 6.54/6.71       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 6.54/6.71  thf('133', plain,
% 6.54/6.71      (![X18 : $i]:
% 6.54/6.71         ((m1_subset_1 @ (k5_lattices @ X18) @ (u1_struct_0 @ X18))
% 6.54/6.71          | ~ (l1_lattices @ X18)
% 6.54/6.71          | (v2_struct_0 @ X18))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.54/6.71  thf('134', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('135', plain,
% 6.54/6.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 6.54/6.71          | ~ (l1_lattices @ X9)
% 6.54/6.71          | ~ (v6_lattices @ X9)
% 6.54/6.71          | (v2_struct_0 @ X9)
% 6.54/6.71          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 6.54/6.71          | ((k4_lattices @ X9 @ X8 @ X10) = (k4_lattices @ X9 @ X10 @ X8)))),
% 6.54/6.71      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 6.54/6.71  thf('136', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71            = (k4_lattices @ sk_A @ X0 @ sk_B_2))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v6_lattices @ sk_A)
% 6.54/6.71          | ~ (l1_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['134', '135'])).
% 6.54/6.71  thf('137', plain, ((v6_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['10', '11', '12'])).
% 6.54/6.71  thf('138', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('139', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71            = (k4_lattices @ sk_A @ X0 @ sk_B_2))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['136', '137', '138'])).
% 6.54/6.71  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('141', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71              = (k4_lattices @ sk_A @ X0 @ sk_B_2)))),
% 6.54/6.71      inference('clc', [status(thm)], ['139', '140'])).
% 6.54/6.71  thf('142', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l1_lattices @ sk_A)
% 6.54/6.71        | ((k4_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71            = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['133', '141'])).
% 6.54/6.71  thf('143', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('144', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k4_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71            = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['142', '143'])).
% 6.54/6.71  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('146', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71         = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['144', '145'])).
% 6.54/6.71  thf('147', plain,
% 6.54/6.71      (![X18 : $i]:
% 6.54/6.71         ((m1_subset_1 @ (k5_lattices @ X18) @ (u1_struct_0 @ X18))
% 6.54/6.71          | ~ (l1_lattices @ X18)
% 6.54/6.71          | (v2_struct_0 @ X18))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.54/6.71  thf('148', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('149', plain,
% 6.54/6.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 6.54/6.71          | ~ (l1_lattices @ X27)
% 6.54/6.71          | ~ (v6_lattices @ X27)
% 6.54/6.71          | (v2_struct_0 @ X27)
% 6.54/6.71          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 6.54/6.71          | ((k4_lattices @ X27 @ X26 @ X28) = (k2_lattices @ X27 @ X26 @ X28)))),
% 6.54/6.71      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 6.54/6.71  thf('150', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71            = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v6_lattices @ sk_A)
% 6.54/6.71          | ~ (l1_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['148', '149'])).
% 6.54/6.71  thf('151', plain, ((v6_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['10', '11', '12'])).
% 6.54/6.71  thf('152', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('153', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71            = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['150', '151', '152'])).
% 6.54/6.71  thf('154', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('155', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71              = (k2_lattices @ sk_A @ sk_B_2 @ X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['153', '154'])).
% 6.54/6.71  thf('156', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l1_lattices @ sk_A)
% 6.54/6.71        | ((k4_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71            = (k2_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))))),
% 6.54/6.71      inference('sup-', [status(thm)], ['147', '155'])).
% 6.54/6.71  thf('157', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('158', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k4_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71            = (k2_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))))),
% 6.54/6.71      inference('demod', [status(thm)], ['156', '157'])).
% 6.54/6.71  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('160', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A)))),
% 6.54/6.71      inference('clc', [status(thm)], ['158', '159'])).
% 6.54/6.71  thf('161', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71         = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_2))),
% 6.54/6.71      inference('demod', [status(thm)], ['146', '160'])).
% 6.54/6.71  thf('162', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k2_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71            = (k5_lattices @ sk_A)))),
% 6.54/6.71      inference('demod', [status(thm)], ['119', '120', '131', '132', '161'])).
% 6.54/6.71  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('164', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_B_2 @ (k5_lattices @ sk_A))
% 6.54/6.71         = (k5_lattices @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['162', '163'])).
% 6.54/6.71  thf('165', plain,
% 6.54/6.71      (((k5_lattices @ sk_A)
% 6.54/6.71         = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['86', '116', '164'])).
% 6.54/6.71  thf('166', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('167', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('168', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('169', plain,
% 6.54/6.71      (![X20 : $i, X21 : $i]:
% 6.54/6.71         (~ (l3_lattices @ X20)
% 6.54/6.71          | (v2_struct_0 @ X20)
% 6.54/6.71          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 6.54/6.71          | (m1_subset_1 @ (k7_lattices @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 6.54/6.71  thf('170', plain,
% 6.54/6.71      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 6.54/6.71        | (v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['168', '169'])).
% 6.54/6.71  thf('171', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('172', plain,
% 6.54/6.71      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 6.54/6.71        | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['170', '171'])).
% 6.54/6.71  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('174', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf('175', plain,
% 6.54/6.71      (![X20 : $i, X21 : $i]:
% 6.54/6.71         (~ (l3_lattices @ X20)
% 6.54/6.71          | (v2_struct_0 @ X20)
% 6.54/6.71          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 6.54/6.71          | (m1_subset_1 @ (k7_lattices @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 6.54/6.71  thf('176', plain,
% 6.54/6.71      (((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) @ 
% 6.54/6.71         (u1_struct_0 @ sk_A))
% 6.54/6.71        | (v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['174', '175'])).
% 6.54/6.71  thf('177', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('178', plain,
% 6.54/6.71      (((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) @ 
% 6.54/6.71         (u1_struct_0 @ sk_A))
% 6.54/6.71        | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['176', '177'])).
% 6.54/6.71  thf('179', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('180', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) @ 
% 6.54/6.71        (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['178', '179'])).
% 6.54/6.71  thf('181', plain,
% 6.54/6.71      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 6.54/6.71         (~ (v7_lattices @ X11)
% 6.54/6.71          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 6.54/6.71          | ((k2_lattices @ X11 @ X13 @ (k2_lattices @ X11 @ X12 @ X14))
% 6.54/6.71              = (k2_lattices @ X11 @ (k2_lattices @ X11 @ X13 @ X12) @ X14))
% 6.54/6.71          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 6.54/6.71          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 6.54/6.71          | ~ (l1_lattices @ X11)
% 6.54/6.71          | (v2_struct_0 @ X11))),
% 6.54/6.71      inference('cnf', [status(esa)], [d7_lattices])).
% 6.54/6.71  thf('182', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (l1_lattices @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ X0 @ 
% 6.54/6.71              (k2_lattices @ sk_A @ 
% 6.54/6.71               (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) @ X1))
% 6.54/6.71              = (k2_lattices @ sk_A @ 
% 6.54/6.71                 (k2_lattices @ sk_A @ X0 @ 
% 6.54/6.71                  (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2))) @ 
% 6.54/6.71                 X1))
% 6.54/6.71          | ~ (v7_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['180', '181'])).
% 6.54/6.71  thf('183', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('184', plain, ((v7_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['67', '68', '69'])).
% 6.54/6.71  thf('185', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ X0 @ 
% 6.54/6.71              (k2_lattices @ sk_A @ 
% 6.54/6.71               (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) @ X1))
% 6.54/6.71              = (k2_lattices @ sk_A @ 
% 6.54/6.71                 (k2_lattices @ sk_A @ X0 @ 
% 6.54/6.71                  (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2))) @ 
% 6.54/6.71                 X1)))),
% 6.54/6.71      inference('demod', [status(thm)], ['182', '183', '184'])).
% 6.54/6.71  thf('186', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('187', plain,
% 6.54/6.71      (![X69 : $i, X70 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X69 @ (u1_struct_0 @ X70))
% 6.54/6.71          | ((k7_lattices @ X70 @ (k7_lattices @ X70 @ X69)) = (X69))
% 6.54/6.71          | ~ (l3_lattices @ X70)
% 6.54/6.71          | ~ (v17_lattices @ X70)
% 6.54/6.71          | ~ (v10_lattices @ X70)
% 6.54/6.71          | (v2_struct_0 @ X70))),
% 6.54/6.71      inference('cnf', [status(esa)], [t49_lattices])).
% 6.54/6.71  thf('188', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (v10_lattices @ sk_A)
% 6.54/6.71        | ~ (v17_lattices @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A)
% 6.54/6.71        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) = (sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['186', '187'])).
% 6.54/6.71  thf('189', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('190', plain, ((v17_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('191', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('192', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) = (sk_B_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 6.54/6.71  thf('193', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('194', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) = (sk_B_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['192', '193'])).
% 6.54/6.71  thf('195', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) = (sk_B_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['192', '193'])).
% 6.54/6.71  thf('196', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_B_2 @ X1))
% 6.54/6.71              = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ X1)))),
% 6.54/6.71      inference('demod', [status(thm)], ['185', '194', '195'])).
% 6.54/6.71  thf('197', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k2_lattices @ sk_A @ sk_C_2 @ (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71            = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['167', '196'])).
% 6.54/6.71  thf('198', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('199', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71              = (k2_lattices @ sk_A @ sk_C_2 @ X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['109', '110'])).
% 6.54/6.71  thf('200', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 6.54/6.71      inference('sup-', [status(thm)], ['198', '199'])).
% 6.54/6.71  thf('201', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('202', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71              = (k4_lattices @ sk_A @ X0 @ sk_B_2)))),
% 6.54/6.71      inference('clc', [status(thm)], ['139', '140'])).
% 6.54/6.71  thf('203', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 6.54/6.71         = (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 6.54/6.71      inference('sup-', [status(thm)], ['201', '202'])).
% 6.54/6.71  thf('204', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('205', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71              = (k2_lattices @ sk_A @ sk_B_2 @ X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['153', '154'])).
% 6.54/6.71  thf('206', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 6.54/6.71      inference('sup-', [status(thm)], ['204', '205'])).
% 6.54/6.71  thf('207', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 6.54/6.71         = (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 6.54/6.71      inference('demod', [status(thm)], ['203', '206'])).
% 6.54/6.71  thf('208', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 6.54/6.71      inference('sup+', [status(thm)], ['200', '207'])).
% 6.54/6.71  thf('209', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k2_lattices @ sk_A @ sk_C_2 @ (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71            = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['197', '208'])).
% 6.54/6.71  thf('210', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('211', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k2_lattices @ sk_A @ sk_C_2 @ (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71              = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ 
% 6.54/6.71                 X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['209', '210'])).
% 6.54/6.71  thf('212', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_C_2 @ 
% 6.54/6.71         (k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))
% 6.54/6.71         = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['166', '211'])).
% 6.54/6.71  thf('213', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_C_2 @ 
% 6.54/6.71         (k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))
% 6.54/6.71         = (k5_lattices @ sk_A))),
% 6.54/6.71      inference('sup+', [status(thm)], ['165', '212'])).
% 6.54/6.71  thf('214', plain,
% 6.54/6.71      ((((k2_lattices @ sk_A @ sk_C_2 @ sk_B_2) = (k5_lattices @ sk_A)))
% 6.54/6.71         <= (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.71      inference('sup+', [status(thm)], ['50', '213'])).
% 6.54/6.71  thf('215', plain,
% 6.54/6.71      (((k2_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 6.54/6.71      inference('sup+', [status(thm)], ['200', '207'])).
% 6.54/6.71  thf('216', plain,
% 6.54/6.71      ((((k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A)))
% 6.54/6.71         <= (((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.71      inference('sup+', [status(thm)], ['214', '215'])).
% 6.54/6.71  thf('217', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 6.54/6.71      inference('sup-', [status(thm)], ['204', '205'])).
% 6.54/6.71  thf('218', plain,
% 6.54/6.71      ((((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) != (k5_lattices @ sk_A)))
% 6.54/6.71         <= (~
% 6.54/6.71             (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A))))),
% 6.54/6.71      inference('split', [status(esa)], ['0'])).
% 6.54/6.71  thf('219', plain,
% 6.54/6.71      ((((k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) != (k5_lattices @ sk_A)))
% 6.54/6.71         <= (~
% 6.54/6.71             (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A))))),
% 6.54/6.71      inference('sup-', [status(thm)], ['217', '218'])).
% 6.54/6.71  thf('220', plain,
% 6.54/6.71      ((((k5_lattices @ sk_A) != (k5_lattices @ sk_A)))
% 6.54/6.71         <= (~
% 6.54/6.71             (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A))) & 
% 6.54/6.71             ((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))))),
% 6.54/6.71      inference('sup-', [status(thm)], ['216', '219'])).
% 6.54/6.71  thf('221', plain,
% 6.54/6.71      ((((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A))) | 
% 6.54/6.71       ~ ((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('simplify', [status(thm)], ['220'])).
% 6.54/6.71  thf('222', plain,
% 6.54/6.71      (~ ((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('sat_resolution*', [status(thm)], ['2', '221'])).
% 6.54/6.71  thf('223', plain,
% 6.54/6.71      (~ (r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))),
% 6.54/6.71      inference('simpl_trail', [status(thm)], ['1', '222'])).
% 6.54/6.71  thf('224', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('225', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('226', plain,
% 6.54/6.71      (![X36 : $i, X37 : $i, X38 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 6.54/6.71          | ((k2_lattices @ X37 @ X36 @ X38) != (X36))
% 6.54/6.71          | (r1_lattices @ X37 @ X36 @ X38)
% 6.54/6.71          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 6.54/6.71          | ~ (l3_lattices @ X37)
% 6.54/6.71          | ~ (v9_lattices @ X37)
% 6.54/6.71          | ~ (v8_lattices @ X37)
% 6.54/6.71          | (v2_struct_0 @ X37))),
% 6.54/6.71      inference('cnf', [status(esa)], [t21_lattices])).
% 6.54/6.71  thf('227', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v8_lattices @ sk_A)
% 6.54/6.71          | ~ (v9_lattices @ sk_A)
% 6.54/6.71          | ~ (l3_lattices @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71          | ((k2_lattices @ sk_A @ sk_B_2 @ X0) != (sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['225', '226'])).
% 6.54/6.71  thf('228', plain, ((v8_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['16', '17', '18'])).
% 6.54/6.71  thf('229', plain, ((v9_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['22', '23', '24'])).
% 6.54/6.71  thf('230', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('231', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71          | ((k2_lattices @ sk_A @ sk_B_2 @ X0) != (sk_B_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['227', '228', '229', '230'])).
% 6.54/6.71  thf('232', plain,
% 6.54/6.71      ((((k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71          != (sk_B_2))
% 6.54/6.71        | (r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71        | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['224', '231'])).
% 6.54/6.71  thf('233', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('234', plain,
% 6.54/6.71      (((r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71        | ((k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71            != (sk_B_2)))),
% 6.54/6.71      inference('clc', [status(thm)], ['232', '233'])).
% 6.54/6.71  thf('235', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('236', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf(t51_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ![C:$i]:
% 6.54/6.71             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71               ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) ) =
% 6.54/6.71                 ( k4_lattices @
% 6.54/6.71                   A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 6.54/6.71  thf('237', plain,
% 6.54/6.71      (![X74 : $i, X75 : $i, X76 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X74 @ (u1_struct_0 @ X75))
% 6.54/6.71          | ((k7_lattices @ X75 @ (k3_lattices @ X75 @ X74 @ X76))
% 6.54/6.71              = (k4_lattices @ X75 @ (k7_lattices @ X75 @ X74) @ 
% 6.54/6.71                 (k7_lattices @ X75 @ X76)))
% 6.54/6.71          | ~ (m1_subset_1 @ X76 @ (u1_struct_0 @ X75))
% 6.54/6.71          | ~ (l3_lattices @ X75)
% 6.54/6.71          | ~ (v17_lattices @ X75)
% 6.54/6.71          | ~ (v10_lattices @ X75)
% 6.54/6.71          | (v2_struct_0 @ X75))),
% 6.54/6.71      inference('cnf', [status(esa)], [t51_lattices])).
% 6.54/6.71  thf('238', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v10_lattices @ sk_A)
% 6.54/6.71          | ~ (v17_lattices @ sk_A)
% 6.54/6.71          | ~ (l3_lattices @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k7_lattices @ sk_A @ 
% 6.54/6.71              (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X0))
% 6.54/6.71              = (k4_lattices @ sk_A @ 
% 6.54/6.71                 (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) @ 
% 6.54/6.71                 (k7_lattices @ sk_A @ X0))))),
% 6.54/6.71      inference('sup-', [status(thm)], ['236', '237'])).
% 6.54/6.71  thf('239', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('240', plain, ((v17_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('241', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('242', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) = (sk_B_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['192', '193'])).
% 6.54/6.71  thf('243', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k7_lattices @ sk_A @ 
% 6.54/6.71              (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X0))
% 6.54/6.71              = (k4_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ X0))))),
% 6.54/6.71      inference('demod', [status(thm)], ['238', '239', '240', '241', '242'])).
% 6.54/6.71  thf('244', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('245', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k7_lattices @ sk_A @ 
% 6.54/6.71            (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X0))
% 6.54/6.71            = (k4_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ X0)))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 6.54/6.71      inference('clc', [status(thm)], ['243', '244'])).
% 6.54/6.71  thf('246', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ 
% 6.54/6.71         (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_C_2))
% 6.54/6.71         = (k4_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['235', '245'])).
% 6.54/6.71  thf('247', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf('248', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(commutativity_k3_lattices, axiom,
% 6.54/6.71    (![A:$i,B:$i,C:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 6.54/6.71         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 6.54/6.71         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 6.54/6.71       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 6.54/6.71  thf('249', plain,
% 6.54/6.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 6.54/6.71          | ~ (l2_lattices @ X6)
% 6.54/6.71          | ~ (v4_lattices @ X6)
% 6.54/6.71          | (v2_struct_0 @ X6)
% 6.54/6.71          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 6.54/6.71          | ((k3_lattices @ X6 @ X5 @ X7) = (k3_lattices @ X6 @ X7 @ X5)))),
% 6.54/6.71      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 6.54/6.71  thf('250', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71            = (k3_lattices @ sk_A @ X0 @ sk_C_2))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v4_lattices @ sk_A)
% 6.54/6.71          | ~ (l2_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['248', '249'])).
% 6.54/6.71  thf('251', plain,
% 6.54/6.71      (![X2 : $i]:
% 6.54/6.71         ((v2_struct_0 @ X2)
% 6.54/6.71          | ~ (v10_lattices @ X2)
% 6.54/6.71          | (v4_lattices @ X2)
% 6.54/6.71          | ~ (l3_lattices @ X2))),
% 6.54/6.71      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.54/6.71  thf('252', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('253', plain,
% 6.54/6.71      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['251', '252'])).
% 6.54/6.71  thf('254', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('255', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('256', plain, ((v4_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['253', '254', '255'])).
% 6.54/6.71  thf('257', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('258', plain,
% 6.54/6.71      (![X22 : $i]: ((l2_lattices @ X22) | ~ (l3_lattices @ X22))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 6.54/6.71  thf('259', plain, ((l2_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['257', '258'])).
% 6.54/6.71  thf('260', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71            = (k3_lattices @ sk_A @ X0 @ sk_C_2))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['250', '256', '259'])).
% 6.54/6.71  thf('261', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('262', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71              = (k3_lattices @ sk_A @ X0 @ sk_C_2)))),
% 6.54/6.71      inference('clc', [status(thm)], ['260', '261'])).
% 6.54/6.71  thf('263', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_C_2))),
% 6.54/6.71      inference('sup-', [status(thm)], ['247', '262'])).
% 6.54/6.71  thf('264', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf('265', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(redefinition_k3_lattices, axiom,
% 6.54/6.71    (![A:$i,B:$i,C:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 6.54/6.71         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 6.54/6.71         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 6.54/6.71       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 6.54/6.71  thf('266', plain,
% 6.54/6.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 6.54/6.71          | ~ (l2_lattices @ X24)
% 6.54/6.71          | ~ (v4_lattices @ X24)
% 6.54/6.71          | (v2_struct_0 @ X24)
% 6.54/6.71          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 6.54/6.71          | ((k3_lattices @ X24 @ X23 @ X25) = (k1_lattices @ X24 @ X23 @ X25)))),
% 6.54/6.71      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 6.54/6.71  thf('267', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71            = (k1_lattices @ sk_A @ sk_C_2 @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v4_lattices @ sk_A)
% 6.54/6.71          | ~ (l2_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['265', '266'])).
% 6.54/6.71  thf('268', plain, ((v4_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['253', '254', '255'])).
% 6.54/6.71  thf('269', plain, ((l2_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['257', '258'])).
% 6.54/6.71  thf('270', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71            = (k1_lattices @ sk_A @ sk_C_2 @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['267', '268', '269'])).
% 6.54/6.71  thf('271', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('272', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71              = (k1_lattices @ sk_A @ sk_C_2 @ X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['270', '271'])).
% 6.54/6.71  thf('273', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['264', '272'])).
% 6.54/6.71  thf('274', plain,
% 6.54/6.71      (((k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_C_2))),
% 6.54/6.71      inference('demod', [status(thm)], ['263', '273'])).
% 6.54/6.71  thf('275', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('276', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71              = (k2_lattices @ sk_A @ sk_B_2 @ X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['153', '154'])).
% 6.54/6.71  thf('277', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['275', '276'])).
% 6.54/6.71  thf('278', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ 
% 6.54/6.71         (k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2)))
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['246', '274', '277'])).
% 6.54/6.71  thf('279', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('280', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('281', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf(t31_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ![C:$i]:
% 6.54/6.71             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71               ( ![D:$i]:
% 6.54/6.71                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71                   ( ( k3_lattices @ A @ B @ ( k4_lattices @ A @ C @ D ) ) =
% 6.54/6.71                     ( k4_lattices @
% 6.54/6.71                       A @ ( k3_lattices @ A @ B @ C ) @ 
% 6.54/6.71                       ( k3_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 6.54/6.71  thf('282', plain,
% 6.54/6.71      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X49 @ (u1_struct_0 @ X50))
% 6.54/6.71          | ~ (m1_subset_1 @ X51 @ (u1_struct_0 @ X50))
% 6.54/6.71          | ((k3_lattices @ X50 @ X49 @ (k4_lattices @ X50 @ X52 @ X51))
% 6.54/6.71              = (k4_lattices @ X50 @ (k3_lattices @ X50 @ X49 @ X52) @ 
% 6.54/6.71                 (k3_lattices @ X50 @ X49 @ X51)))
% 6.54/6.71          | ~ (m1_subset_1 @ X52 @ (u1_struct_0 @ X50))
% 6.54/6.71          | ~ (l3_lattices @ X50)
% 6.54/6.71          | ~ (v11_lattices @ X50)
% 6.54/6.71          | ~ (v10_lattices @ X50)
% 6.54/6.71          | (v2_struct_0 @ X50))),
% 6.54/6.71      inference('cnf', [status(esa)], [t31_lattices])).
% 6.54/6.71  thf('283', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v10_lattices @ sk_A)
% 6.54/6.71          | ~ (v11_lattices @ sk_A)
% 6.54/6.71          | ~ (l3_lattices @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71              (k4_lattices @ sk_A @ X0 @ X1))
% 6.54/6.71              = (k4_lattices @ sk_A @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X0) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X1)))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['281', '282'])).
% 6.54/6.71  thf('284', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('285', plain,
% 6.54/6.71      (![X4 : $i]:
% 6.54/6.71         ((v2_struct_0 @ X4)
% 6.54/6.71          | ~ (v17_lattices @ X4)
% 6.54/6.71          | (v11_lattices @ X4)
% 6.54/6.71          | ~ (l3_lattices @ X4))),
% 6.54/6.71      inference('cnf', [status(esa)], [cc5_lattices])).
% 6.54/6.71  thf('286', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('287', plain,
% 6.54/6.71      ((~ (l3_lattices @ sk_A)
% 6.54/6.71        | (v11_lattices @ sk_A)
% 6.54/6.71        | ~ (v17_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['285', '286'])).
% 6.54/6.71  thf('288', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('289', plain, ((v17_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('290', plain, ((v11_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['287', '288', '289'])).
% 6.54/6.71  thf('291', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('292', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71              (k4_lattices @ sk_A @ X0 @ X1))
% 6.54/6.71              = (k4_lattices @ sk_A @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X0) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X1)))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.54/6.71      inference('demod', [status(thm)], ['283', '284', '290', '291'])).
% 6.54/6.71  thf('293', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71              (k4_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71              = (k4_lattices @ sk_A @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X0)))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['280', '292'])).
% 6.54/6.71  thf('294', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf('295', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('296', plain,
% 6.54/6.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 6.54/6.71          | ~ (l2_lattices @ X6)
% 6.54/6.71          | ~ (v4_lattices @ X6)
% 6.54/6.71          | (v2_struct_0 @ X6)
% 6.54/6.71          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 6.54/6.71          | ((k3_lattices @ X6 @ X5 @ X7) = (k3_lattices @ X6 @ X7 @ X5)))),
% 6.54/6.71      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 6.54/6.71  thf('297', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71            = (k3_lattices @ sk_A @ X0 @ sk_B_2))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v4_lattices @ sk_A)
% 6.54/6.71          | ~ (l2_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['295', '296'])).
% 6.54/6.71  thf('298', plain, ((v4_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['253', '254', '255'])).
% 6.54/6.71  thf('299', plain, ((l2_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['257', '258'])).
% 6.54/6.71  thf('300', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71            = (k3_lattices @ sk_A @ X0 @ sk_B_2))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['297', '298', '299'])).
% 6.54/6.71  thf('301', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('302', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71              = (k3_lattices @ sk_A @ X0 @ sk_B_2)))),
% 6.54/6.71      inference('clc', [status(thm)], ['300', '301'])).
% 6.54/6.71  thf('303', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_B_2))),
% 6.54/6.71      inference('sup-', [status(thm)], ['294', '302'])).
% 6.54/6.71  thf('304', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf('305', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('306', plain,
% 6.54/6.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 6.54/6.71          | ~ (l2_lattices @ X24)
% 6.54/6.71          | ~ (v4_lattices @ X24)
% 6.54/6.71          | (v2_struct_0 @ X24)
% 6.54/6.71          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 6.54/6.71          | ((k3_lattices @ X24 @ X23 @ X25) = (k1_lattices @ X24 @ X23 @ X25)))),
% 6.54/6.71      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 6.54/6.71  thf('307', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71            = (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v4_lattices @ sk_A)
% 6.54/6.71          | ~ (l2_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['305', '306'])).
% 6.54/6.71  thf('308', plain, ((v4_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['253', '254', '255'])).
% 6.54/6.71  thf('309', plain, ((l2_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['257', '258'])).
% 6.54/6.71  thf('310', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71            = (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['307', '308', '309'])).
% 6.54/6.71  thf('311', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('312', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71              = (k1_lattices @ sk_A @ sk_B_2 @ X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['310', '311'])).
% 6.54/6.71  thf('313', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['304', '312'])).
% 6.54/6.71  thf('314', plain,
% 6.54/6.71      (((k1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_B_2))),
% 6.54/6.71      inference('demod', [status(thm)], ['303', '313'])).
% 6.54/6.71  thf('315', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(t48_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ B ) =
% 6.54/6.71             ( k6_lattices @ A ) ) ) ) ))).
% 6.54/6.71  thf('316', plain,
% 6.54/6.71      (![X67 : $i, X68 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X67 @ (u1_struct_0 @ X68))
% 6.54/6.71          | ((k3_lattices @ X68 @ (k7_lattices @ X68 @ X67) @ X67)
% 6.54/6.71              = (k6_lattices @ X68))
% 6.54/6.71          | ~ (l3_lattices @ X68)
% 6.54/6.71          | ~ (v17_lattices @ X68)
% 6.54/6.71          | ~ (v10_lattices @ X68)
% 6.54/6.71          | (v2_struct_0 @ X68))),
% 6.54/6.71      inference('cnf', [status(esa)], [t48_lattices])).
% 6.54/6.71  thf('317', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (v10_lattices @ sk_A)
% 6.54/6.71        | ~ (v17_lattices @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_B_2)
% 6.54/6.71            = (k6_lattices @ sk_A)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['315', '316'])).
% 6.54/6.71  thf('318', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('319', plain, ((v17_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('320', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('321', plain,
% 6.54/6.71      (((k1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_B_2))),
% 6.54/6.71      inference('demod', [status(thm)], ['303', '313'])).
% 6.54/6.71  thf('322', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71            = (k6_lattices @ sk_A)))),
% 6.54/6.71      inference('demod', [status(thm)], ['317', '318', '319', '320', '321'])).
% 6.54/6.71  thf('323', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('324', plain,
% 6.54/6.71      (((k1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k6_lattices @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['322', '323'])).
% 6.54/6.71  thf('325', plain,
% 6.54/6.71      (((k6_lattices @ sk_A)
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_B_2))),
% 6.54/6.71      inference('demod', [status(thm)], ['314', '324'])).
% 6.54/6.71  thf('326', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71              (k4_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71              = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X0)))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['293', '325'])).
% 6.54/6.71  thf('327', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('328', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71            (k4_lattices @ sk_A @ sk_B_2 @ X0))
% 6.54/6.71            = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71               (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ X0)))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 6.54/6.71      inference('clc', [status(thm)], ['326', '327'])).
% 6.54/6.71  thf('329', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71         (k4_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 6.54/6.71         = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71            (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_C_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['279', '328'])).
% 6.54/6.71  thf('330', plain,
% 6.54/6.71      ((((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A)))
% 6.54/6.71         <= ((((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A))))),
% 6.54/6.71      inference('split', [status(esa)], ['3'])).
% 6.54/6.71  thf('331', plain,
% 6.54/6.71      ((((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A))) | 
% 6.54/6.71       ((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('split', [status(esa)], ['3'])).
% 6.54/6.71  thf('332', plain,
% 6.54/6.71      ((((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A)))),
% 6.54/6.71      inference('sat_resolution*', [status(thm)], ['2', '221', '331'])).
% 6.54/6.71  thf('333', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (k5_lattices @ sk_A))),
% 6.54/6.71      inference('simpl_trail', [status(thm)], ['330', '332'])).
% 6.54/6.71  thf('334', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf('335', plain,
% 6.54/6.71      (![X18 : $i]:
% 6.54/6.71         ((m1_subset_1 @ (k5_lattices @ X18) @ (u1_struct_0 @ X18))
% 6.54/6.71          | ~ (l1_lattices @ X18)
% 6.54/6.71          | (v2_struct_0 @ X18))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.54/6.71  thf('336', plain,
% 6.54/6.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 6.54/6.71          | ~ (l2_lattices @ X6)
% 6.54/6.71          | ~ (v4_lattices @ X6)
% 6.54/6.71          | (v2_struct_0 @ X6)
% 6.54/6.71          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 6.54/6.71          | ((k3_lattices @ X6 @ X5 @ X7) = (k3_lattices @ X6 @ X7 @ X5)))),
% 6.54/6.71      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 6.54/6.71  thf('337', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ X0)
% 6.54/6.71          | ~ (l1_lattices @ X0)
% 6.54/6.71          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 6.54/6.71              = (k3_lattices @ X0 @ X1 @ (k5_lattices @ X0)))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.54/6.71          | (v2_struct_0 @ X0)
% 6.54/6.71          | ~ (v4_lattices @ X0)
% 6.54/6.71          | ~ (l2_lattices @ X0))),
% 6.54/6.71      inference('sup-', [status(thm)], ['335', '336'])).
% 6.54/6.71  thf('338', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         (~ (l2_lattices @ X0)
% 6.54/6.71          | ~ (v4_lattices @ X0)
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.54/6.71          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 6.54/6.71              = (k3_lattices @ X0 @ X1 @ (k5_lattices @ X0)))
% 6.54/6.71          | ~ (l1_lattices @ X0)
% 6.54/6.71          | (v2_struct_0 @ X0))),
% 6.54/6.71      inference('simplify', [status(thm)], ['337'])).
% 6.54/6.71  thf('339', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l1_lattices @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71            = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71               (k5_lattices @ sk_A)))
% 6.54/6.71        | ~ (v4_lattices @ sk_A)
% 6.54/6.71        | ~ (l2_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['334', '338'])).
% 6.54/6.71  thf('340', plain, ((l1_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['62', '63'])).
% 6.54/6.71  thf('341', plain, ((v4_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['253', '254', '255'])).
% 6.54/6.71  thf('342', plain, ((l2_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['257', '258'])).
% 6.54/6.71  thf('343', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71            = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71               (k5_lattices @ sk_A))))),
% 6.54/6.71      inference('demod', [status(thm)], ['339', '340', '341', '342'])).
% 6.54/6.71  thf('344', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('345', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.54/6.71         (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71            (k5_lattices @ sk_A)))),
% 6.54/6.71      inference('clc', [status(thm)], ['343', '344'])).
% 6.54/6.71  thf('346', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf(t39_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 6.54/6.71  thf('347', plain,
% 6.54/6.71      (![X57 : $i, X58 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X57 @ (u1_struct_0 @ X58))
% 6.54/6.71          | ((k3_lattices @ X58 @ (k5_lattices @ X58) @ X57) = (X57))
% 6.54/6.71          | ~ (l3_lattices @ X58)
% 6.54/6.71          | ~ (v13_lattices @ X58)
% 6.54/6.71          | ~ (v10_lattices @ X58)
% 6.54/6.71          | (v2_struct_0 @ X58))),
% 6.54/6.71      inference('cnf', [status(esa)], [t39_lattices])).
% 6.54/6.71  thf('348', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (v10_lattices @ sk_A)
% 6.54/6.71        | ~ (v13_lattices @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_B_2)) = (k7_lattices @ sk_A @ sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['346', '347'])).
% 6.54/6.71  thf('349', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('350', plain, ((v13_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['123', '124', '130'])).
% 6.54/6.71  thf('351', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('352', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_B_2)) = (k7_lattices @ sk_A @ sk_B_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['348', '349', '350', '351'])).
% 6.54/6.71  thf('353', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('354', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.54/6.71         (k7_lattices @ sk_A @ sk_B_2)) = (k7_lattices @ sk_A @ sk_B_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['352', '353'])).
% 6.54/6.71  thf('355', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ sk_B_2)
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ 
% 6.54/6.71            (k5_lattices @ sk_A)))),
% 6.54/6.71      inference('demod', [status(thm)], ['345', '354'])).
% 6.54/6.71  thf('356', plain,
% 6.54/6.71      (((k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2) @ sk_C_2))),
% 6.54/6.71      inference('demod', [status(thm)], ['263', '273'])).
% 6.54/6.71  thf('357', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ sk_B_2)
% 6.54/6.71         = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71            (k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))))),
% 6.54/6.71      inference('demod', [status(thm)], ['329', '333', '355', '356'])).
% 6.54/6.71  thf('358', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf(dt_k6_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 6.54/6.71       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 6.54/6.71  thf('359', plain,
% 6.54/6.71      (![X19 : $i]:
% 6.54/6.71         ((m1_subset_1 @ (k6_lattices @ X19) @ (u1_struct_0 @ X19))
% 6.54/6.71          | ~ (l2_lattices @ X19)
% 6.54/6.71          | (v2_struct_0 @ X19))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 6.54/6.71  thf('360', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('361', plain,
% 6.54/6.71      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X49 @ (u1_struct_0 @ X50))
% 6.54/6.71          | ~ (m1_subset_1 @ X51 @ (u1_struct_0 @ X50))
% 6.54/6.71          | ((k3_lattices @ X50 @ X49 @ (k4_lattices @ X50 @ X52 @ X51))
% 6.54/6.71              = (k4_lattices @ X50 @ (k3_lattices @ X50 @ X49 @ X52) @ 
% 6.54/6.71                 (k3_lattices @ X50 @ X49 @ X51)))
% 6.54/6.71          | ~ (m1_subset_1 @ X52 @ (u1_struct_0 @ X50))
% 6.54/6.71          | ~ (l3_lattices @ X50)
% 6.54/6.71          | ~ (v11_lattices @ X50)
% 6.54/6.71          | ~ (v10_lattices @ X50)
% 6.54/6.71          | (v2_struct_0 @ X50))),
% 6.54/6.71      inference('cnf', [status(esa)], [t31_lattices])).
% 6.54/6.71  thf('362', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v10_lattices @ sk_A)
% 6.54/6.71          | ~ (v11_lattices @ sk_A)
% 6.54/6.71          | ~ (l3_lattices @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_C_2 @ (k4_lattices @ sk_A @ X0 @ X1))
% 6.54/6.71              = (k4_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C_2 @ X0) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ sk_C_2 @ X1)))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['360', '361'])).
% 6.54/6.71  thf('363', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('364', plain, ((v11_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['287', '288', '289'])).
% 6.54/6.71  thf('365', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('366', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_C_2 @ (k4_lattices @ sk_A @ X0 @ X1))
% 6.54/6.71              = (k4_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C_2 @ X0) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ sk_C_2 @ X1)))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.54/6.71      inference('demod', [status(thm)], ['362', '363', '364', '365'])).
% 6.54/6.71  thf('367', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (l2_lattices @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_C_2 @ 
% 6.54/6.71              (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ X0))
% 6.54/6.71              = (k4_lattices @ sk_A @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A)) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ sk_C_2 @ X0)))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['359', '366'])).
% 6.54/6.71  thf('368', plain, ((l2_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['257', '258'])).
% 6.54/6.71  thf('369', plain,
% 6.54/6.71      (![X19 : $i]:
% 6.54/6.71         ((m1_subset_1 @ (k6_lattices @ X19) @ (u1_struct_0 @ X19))
% 6.54/6.71          | ~ (l2_lattices @ X19)
% 6.54/6.71          | (v2_struct_0 @ X19))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 6.54/6.71  thf('370', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 6.54/6.71              = (k1_lattices @ sk_A @ sk_C_2 @ X0)))),
% 6.54/6.71      inference('clc', [status(thm)], ['270', '271'])).
% 6.54/6.71  thf('371', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l2_lattices @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))
% 6.54/6.71            = (k1_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))))),
% 6.54/6.71      inference('sup-', [status(thm)], ['369', '370'])).
% 6.54/6.71  thf('372', plain, ((l2_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['257', '258'])).
% 6.54/6.71  thf('373', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))
% 6.54/6.71            = (k1_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))))),
% 6.54/6.71      inference('demod', [status(thm)], ['371', '372'])).
% 6.54/6.71  thf('374', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('375', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))
% 6.54/6.71         = (k1_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A)))),
% 6.54/6.71      inference('clc', [status(thm)], ['373', '374'])).
% 6.54/6.71  thf('376', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf(t44_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 6.54/6.71             ( k6_lattices @ A ) ) ) ) ))).
% 6.54/6.71  thf('377', plain,
% 6.54/6.71      (![X63 : $i, X64 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X63 @ (u1_struct_0 @ X64))
% 6.54/6.71          | ((k3_lattices @ X64 @ (k6_lattices @ X64) @ X63)
% 6.54/6.71              = (k6_lattices @ X64))
% 6.54/6.71          | ~ (l3_lattices @ X64)
% 6.54/6.71          | ~ (v14_lattices @ X64)
% 6.54/6.71          | ~ (v10_lattices @ X64)
% 6.54/6.71          | (v2_struct_0 @ X64))),
% 6.54/6.71      inference('cnf', [status(esa)], [t44_lattices])).
% 6.54/6.71  thf('378', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (v10_lattices @ sk_A)
% 6.54/6.71        | ~ (v14_lattices @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_C_2)
% 6.54/6.71            = (k6_lattices @ sk_A)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['376', '377'])).
% 6.54/6.71  thf('379', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('380', plain,
% 6.54/6.71      (![X3 : $i]:
% 6.54/6.71         ((v2_struct_0 @ X3)
% 6.54/6.71          | ~ (v15_lattices @ X3)
% 6.54/6.71          | (v14_lattices @ X3)
% 6.54/6.71          | ~ (l3_lattices @ X3))),
% 6.54/6.71      inference('cnf', [status(esa)], [cc4_lattices])).
% 6.54/6.71  thf('381', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('382', plain,
% 6.54/6.71      ((~ (l3_lattices @ sk_A)
% 6.54/6.71        | (v14_lattices @ sk_A)
% 6.54/6.71        | ~ (v15_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['380', '381'])).
% 6.54/6.71  thf('383', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('384', plain, ((v15_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['127', '128', '129'])).
% 6.54/6.71  thf('385', plain, ((v14_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['382', '383', '384'])).
% 6.54/6.71  thf('386', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('387', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('388', plain,
% 6.54/6.71      (![X19 : $i]:
% 6.54/6.71         ((m1_subset_1 @ (k6_lattices @ X19) @ (u1_struct_0 @ X19))
% 6.54/6.71          | ~ (l2_lattices @ X19)
% 6.54/6.71          | (v2_struct_0 @ X19))),
% 6.54/6.71      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 6.54/6.71  thf('389', plain,
% 6.54/6.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 6.54/6.71          | ~ (l2_lattices @ X6)
% 6.54/6.71          | ~ (v4_lattices @ X6)
% 6.54/6.71          | (v2_struct_0 @ X6)
% 6.54/6.71          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 6.54/6.71          | ((k3_lattices @ X6 @ X5 @ X7) = (k3_lattices @ X6 @ X7 @ X5)))),
% 6.54/6.71      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 6.54/6.71  thf('390', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         ((v2_struct_0 @ X0)
% 6.54/6.71          | ~ (l2_lattices @ X0)
% 6.54/6.71          | ((k3_lattices @ X0 @ (k6_lattices @ X0) @ X1)
% 6.54/6.71              = (k3_lattices @ X0 @ X1 @ (k6_lattices @ X0)))
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.54/6.71          | (v2_struct_0 @ X0)
% 6.54/6.71          | ~ (v4_lattices @ X0)
% 6.54/6.71          | ~ (l2_lattices @ X0))),
% 6.54/6.71      inference('sup-', [status(thm)], ['388', '389'])).
% 6.54/6.71  thf('391', plain,
% 6.54/6.71      (![X0 : $i, X1 : $i]:
% 6.54/6.71         (~ (v4_lattices @ X0)
% 6.54/6.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.54/6.71          | ((k3_lattices @ X0 @ (k6_lattices @ X0) @ X1)
% 6.54/6.71              = (k3_lattices @ X0 @ X1 @ (k6_lattices @ X0)))
% 6.54/6.71          | ~ (l2_lattices @ X0)
% 6.54/6.71          | (v2_struct_0 @ X0))),
% 6.54/6.71      inference('simplify', [status(thm)], ['390'])).
% 6.54/6.71  thf('392', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (l2_lattices @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_C_2)
% 6.54/6.71            = (k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A)))
% 6.54/6.71        | ~ (v4_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['387', '391'])).
% 6.54/6.71  thf('393', plain, ((l2_lattices @ sk_A)),
% 6.54/6.71      inference('sup-', [status(thm)], ['257', '258'])).
% 6.54/6.71  thf('394', plain, ((v4_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['253', '254', '255'])).
% 6.54/6.71  thf('395', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_C_2)
% 6.54/6.71            = (k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))))),
% 6.54/6.71      inference('demod', [status(thm)], ['392', '393', '394'])).
% 6.54/6.71  thf('396', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('397', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_C_2)
% 6.54/6.71         = (k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A)))),
% 6.54/6.71      inference('clc', [status(thm)], ['395', '396'])).
% 6.54/6.71  thf('398', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))
% 6.54/6.71         = (k1_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A)))),
% 6.54/6.71      inference('clc', [status(thm)], ['373', '374'])).
% 6.54/6.71  thf('399', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_C_2)
% 6.54/6.71         = (k1_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A)))),
% 6.54/6.71      inference('demod', [status(thm)], ['397', '398'])).
% 6.54/6.71  thf('400', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k1_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))
% 6.54/6.71            = (k6_lattices @ sk_A)))),
% 6.54/6.71      inference('demod', [status(thm)], ['378', '379', '385', '386', '399'])).
% 6.54/6.71  thf('401', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('402', plain,
% 6.54/6.71      (((k1_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))
% 6.54/6.71         = (k6_lattices @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['400', '401'])).
% 6.54/6.71  thf('403', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_C_2 @ (k6_lattices @ sk_A))
% 6.54/6.71         = (k6_lattices @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['375', '402'])).
% 6.54/6.71  thf('404', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         ((v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_C_2 @ 
% 6.54/6.71              (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ X0))
% 6.54/6.71              = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ sk_C_2 @ X0)))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['367', '368', '403'])).
% 6.54/6.71  thf('405', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (((k3_lattices @ sk_A @ sk_C_2 @ 
% 6.54/6.71            (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ X0))
% 6.54/6.71            = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71               (k3_lattices @ sk_A @ sk_C_2 @ X0)))
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('simplify', [status(thm)], ['404'])).
% 6.54/6.71  thf('406', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('407', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | ((k3_lattices @ sk_A @ sk_C_2 @ 
% 6.54/6.71              (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ X0))
% 6.54/6.71              = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71                 (k3_lattices @ sk_A @ sk_C_2 @ X0))))),
% 6.54/6.71      inference('clc', [status(thm)], ['405', '406'])).
% 6.54/6.71  thf('408', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_C_2 @ 
% 6.54/6.71         (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71          (k7_lattices @ sk_A @ sk_B_2)))
% 6.54/6.71         = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71            (k3_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))))),
% 6.54/6.71      inference('sup-', [status(thm)], ['358', '407'])).
% 6.54/6.71  thf('409', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['172', '173'])).
% 6.54/6.71  thf(t43_lattices, axiom,
% 6.54/6.71    (![A:$i]:
% 6.54/6.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.54/6.71         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.54/6.71       ( ![B:$i]:
% 6.54/6.71         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.54/6.71           ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 6.54/6.71  thf('410', plain,
% 6.54/6.71      (![X61 : $i, X62 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X61 @ (u1_struct_0 @ X62))
% 6.54/6.71          | ((k4_lattices @ X62 @ (k6_lattices @ X62) @ X61) = (X61))
% 6.54/6.71          | ~ (l3_lattices @ X62)
% 6.54/6.71          | ~ (v14_lattices @ X62)
% 6.54/6.71          | ~ (v10_lattices @ X62)
% 6.54/6.71          | (v2_struct_0 @ X62))),
% 6.54/6.71      inference('cnf', [status(esa)], [t43_lattices])).
% 6.54/6.71  thf('411', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (v10_lattices @ sk_A)
% 6.54/6.71        | ~ (v14_lattices @ sk_A)
% 6.54/6.71        | ~ (l3_lattices @ sk_A)
% 6.54/6.71        | ((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_B_2)) = (k7_lattices @ sk_A @ sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['409', '410'])).
% 6.54/6.71  thf('412', plain, ((v10_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('413', plain, ((v14_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['382', '383', '384'])).
% 6.54/6.71  thf('414', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('415', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71            (k7_lattices @ sk_A @ sk_B_2)) = (k7_lattices @ sk_A @ sk_B_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['411', '412', '413', '414'])).
% 6.54/6.71  thf('416', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('417', plain,
% 6.54/6.71      (((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71         (k7_lattices @ sk_A @ sk_B_2)) = (k7_lattices @ sk_A @ sk_B_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['415', '416'])).
% 6.54/6.71  thf('418', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['264', '272'])).
% 6.54/6.71  thf('419', plain,
% 6.54/6.71      (((k3_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['264', '272'])).
% 6.54/6.71  thf('420', plain,
% 6.54/6.71      (((k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ 
% 6.54/6.71            (k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))))),
% 6.54/6.71      inference('demod', [status(thm)], ['408', '417', '418', '419'])).
% 6.54/6.71  thf('421', plain,
% 6.54/6.71      (((k1_lattices @ sk_A @ sk_C_2 @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k7_lattices @ sk_A @ sk_B_2))),
% 6.54/6.71      inference('sup+', [status(thm)], ['357', '420'])).
% 6.54/6.71  thf('422', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2))
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['278', '421'])).
% 6.54/6.71  thf('423', plain,
% 6.54/6.71      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_2)) = (sk_B_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['192', '193'])).
% 6.54/6.71  thf('424', plain,
% 6.54/6.71      (((sk_B_2)
% 6.54/6.71         = (k2_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['422', '423'])).
% 6.54/6.71  thf('425', plain,
% 6.54/6.71      (((r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))
% 6.54/6.71        | ((sk_B_2) != (sk_B_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['234', '424'])).
% 6.54/6.71  thf('426', plain,
% 6.54/6.71      ((r1_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))),
% 6.54/6.71      inference('simplify', [status(thm)], ['425'])).
% 6.54/6.71  thf('427', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('428', plain,
% 6.54/6.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.54/6.71         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 6.54/6.71          | ~ (l3_lattices @ X30)
% 6.54/6.71          | ~ (v9_lattices @ X30)
% 6.54/6.71          | ~ (v8_lattices @ X30)
% 6.54/6.71          | ~ (v6_lattices @ X30)
% 6.54/6.71          | (v2_struct_0 @ X30)
% 6.54/6.71          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 6.54/6.71          | (r3_lattices @ X30 @ X29 @ X31)
% 6.54/6.71          | ~ (r1_lattices @ X30 @ X29 @ X31))),
% 6.54/6.71      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 6.54/6.71  thf('429', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71          | (r3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A)
% 6.54/6.71          | ~ (v6_lattices @ sk_A)
% 6.54/6.71          | ~ (v8_lattices @ sk_A)
% 6.54/6.71          | ~ (v9_lattices @ sk_A)
% 6.54/6.71          | ~ (l3_lattices @ sk_A))),
% 6.54/6.71      inference('sup-', [status(thm)], ['427', '428'])).
% 6.54/6.71  thf('430', plain, ((v6_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['10', '11', '12'])).
% 6.54/6.71  thf('431', plain, ((v8_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['16', '17', '18'])).
% 6.54/6.71  thf('432', plain, ((v9_lattices @ sk_A)),
% 6.54/6.71      inference('demod', [status(thm)], ['22', '23', '24'])).
% 6.54/6.71  thf('433', plain, ((l3_lattices @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('434', plain,
% 6.54/6.71      (![X0 : $i]:
% 6.54/6.71         (~ (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71          | (r3_lattices @ sk_A @ sk_B_2 @ X0)
% 6.54/6.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.54/6.71          | (v2_struct_0 @ sk_A))),
% 6.54/6.71      inference('demod', [status(thm)], ['429', '430', '431', '432', '433'])).
% 6.54/6.71  thf('435', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 6.54/6.71        | (r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('sup-', [status(thm)], ['426', '434'])).
% 6.54/6.71  thf('436', plain,
% 6.54/6.71      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 6.54/6.71      inference('clc', [status(thm)], ['33', '34'])).
% 6.54/6.71  thf('437', plain,
% 6.54/6.71      (((v2_struct_0 @ sk_A)
% 6.54/6.71        | (r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2)))),
% 6.54/6.71      inference('demod', [status(thm)], ['435', '436'])).
% 6.54/6.71  thf('438', plain, (~ (v2_struct_0 @ sk_A)),
% 6.54/6.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.54/6.71  thf('439', plain,
% 6.54/6.71      ((r3_lattices @ sk_A @ sk_B_2 @ (k7_lattices @ sk_A @ sk_C_2))),
% 6.54/6.71      inference('clc', [status(thm)], ['437', '438'])).
% 6.54/6.71  thf('440', plain, ($false), inference('demod', [status(thm)], ['223', '439'])).
% 6.54/6.71  
% 6.54/6.71  % SZS output end Refutation
% 6.54/6.71  
% 6.57/6.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
