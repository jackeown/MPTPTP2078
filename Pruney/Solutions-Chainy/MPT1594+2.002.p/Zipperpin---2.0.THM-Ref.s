%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sBEcdhyMvu

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  173 (1158 expanded)
%              Number of leaves         :   36 ( 408 expanded)
%              Depth                    :   24
%              Number of atoms          : 1383 (11012 expanded)
%              Number of equality atoms :   24 ( 276 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k4_lattice3_type,type,(
    k4_lattice3: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_lattice3_type,type,(
    k5_lattice3: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t2_yellow_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
         => ( ( r3_orders_2 @ ( k3_yellow_1 @ A ) @ B @ C )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
           => ( ( r3_orders_2 @ ( k3_yellow_1 @ A ) @ B @ C )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_yellow_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('6',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(dt_k5_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ ( k3_lattice3 @ X10 ) ) )
      | ( m1_subset_1 @ ( k5_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( m1_subset_1 @ ( k5_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 ) @ ( u1_struct_0 @ ( k1_lattice3 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( v10_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('9',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf(dt_k1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( m1_subset_1 @ ( k5_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 ) @ ( u1_struct_0 @ ( k1_lattice3 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(fc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( v3_lattices @ ( k1_lattice3 @ A ) )
      & ~ ( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k5_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 ) @ ( u1_struct_0 @ ( k1_lattice3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k5_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(d4_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) )
         => ( ( k5_lattice3 @ A @ B )
            = B ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ ( k3_lattice3 @ X7 ) ) )
      | ( ( k5_lattice3 @ X7 @ X6 )
        = X6 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_lattice3])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( ( k5_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('20',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ( ( k5_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k5_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k5_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 ) @ ( u1_struct_0 @ ( k1_lattice3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('28',plain,(
    m1_subset_1 @ ( k5_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C ) @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_lattice3 @ ( k1_lattice3 @ X0 ) @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('31',plain,
    ( ( k5_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(t2_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
         => ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k1_lattice3 @ X17 ) ) )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ( r1_lattices @ ( k1_lattice3 @ X17 ) @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ ( k1_lattice3 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t2_lattice3])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ X0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','24'])).

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

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v9_lattices @ X2 )
      | ~ ( v8_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r3_lattices @ X2 @ X1 @ X3 )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v6_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v8_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v9_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

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

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('41',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( v6_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('44',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('45',plain,(
    ! [X0: $i] :
      ( v6_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('47',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( v8_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('50',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('51',plain,(
    ! [X0: $i] :
      ( v8_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('53',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) )
      | ( v9_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('56',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('57',plain,(
    ! [X0: $i] :
      ( v9_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','45','51','57','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['36','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('62',plain,
    ( ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('64',plain,
    ( ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','24'])).

thf(t7_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_lattices @ A @ B @ C )
              <=> ( r3_orders_2 @ ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ ( k4_lattice3 @ A @ C ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r3_lattices @ X20 @ X19 @ X21 )
      | ( r3_orders_2 @ ( k3_lattice3 @ X20 ) @ ( k4_lattice3 @ X20 @ X19 ) @ ( k4_lattice3 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_lattice3])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ ( k1_lattice3 @ sk_A ) ) @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B ) @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ X0 ) )
      | ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('70',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('71',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','24'])).

thf(d3_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattice3 @ A @ B )
            = B ) ) ) )).

thf('73',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( ( k4_lattice3 @ X5 @ X4 )
        = X4 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('74',plain,
    ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
    | ~ ( v10_lattices @ ( k1_lattice3 @ sk_A ) )
    | ~ ( l3_lattices @ ( k1_lattice3 @ sk_A ) )
    | ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('76',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('77',plain,
    ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
    | ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('79',plain,
    ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ X0 ) )
      | ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','79'])).

thf('81',plain,
    ( ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C ) )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('83',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( ( k4_lattice3 @ X5 @ X4 )
        = X4 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('84',plain,
    ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
    | ~ ( v10_lattices @ ( k1_lattice3 @ sk_A ) )
    | ~ ( l3_lattices @ ( k1_lattice3 @ sk_A ) )
    | ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('86',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('87',plain,
    ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
    | ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('89',plain,
    ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','89'])).

thf('91',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('92',plain,
    ( ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    | ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['64','92'])).

thf('94',plain,
    ( ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
   <= ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','95'])).

thf('97',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('100',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k1_lattice3 @ X17 ) ) )
      | ~ ( r1_lattices @ ( k1_lattice3 @ X17 ) @ X18 @ X16 )
      | ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ ( k1_lattice3 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t2_lattice3])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['87','88'])).

thf('104',plain,
    ( ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(clc,[status(thm)],['77','78'])).

thf('105',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ X20 ) @ ( k4_lattice3 @ X20 @ X19 ) @ ( k4_lattice3 @ X20 @ X21 ) )
      | ( r3_lattices @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_lattice3])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ ( k1_lattice3 @ sk_A ) ) @ sk_B @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X22: $i] :
      ( ( k3_yellow_1 @ X22 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('108',plain,(
    ! [X15: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('109',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k4_lattice3 @ ( k1_lattice3 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,
    ( ~ ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    | ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,
    ( ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
   <= ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('114',plain,
    ( ( r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('115',plain,(
    r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','95','114'])).

thf('116',plain,(
    r3_orders_2 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['113','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('118',plain,
    ( ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','116','117'])).

thf('119',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('120',plain,(
    r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('122',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v9_lattices @ X2 )
      | ~ ( v8_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r1_lattices @ X2 @ X1 @ X3 )
      | ~ ( r3_lattices @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v6_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v8_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( v9_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( v6_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('125',plain,(
    ! [X0: $i] :
      ( v8_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v9_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('127',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['120','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('131',plain,
    ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('133',plain,(
    r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['102','133'])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['97','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sBEcdhyMvu
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 81 iterations in 0.045s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.50  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.50  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.50  thf(k4_lattice3_type, type, k4_lattice3: $i > $i > $i).
% 0.21/0.50  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k5_lattice3_type, type, k5_lattice3: $i > $i > $i).
% 0.21/0.50  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.50  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.50  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.21/0.50  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.50  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.50  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.50  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.50  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(t2_yellow_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.21/0.50           ( ( r3_orders_2 @ ( k3_yellow_1 @ A ) @ B @ C ) <=>
% 0.21/0.50             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.21/0.50          ( ![C:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.21/0.50              ( ( r3_orders_2 @ ( k3_yellow_1 @ A ) @ B @ C ) <=>
% 0.21/0.50                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t2_yellow_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.21/0.50        | ~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.21/0.50       ~ ((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.50        | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d2_yellow_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.50  thf(dt_k5_lattice3, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.50         ( l3_lattices @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k5_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (l3_lattices @ X10)
% 0.21/0.50          | ~ (v10_lattices @ X10)
% 0.21/0.50          | (v2_struct_0 @ X10)
% 0.21/0.50          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ (k3_lattice3 @ X10)))
% 0.21/0.50          | (m1_subset_1 @ (k5_lattice3 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k5_lattice3])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.21/0.50          | (m1_subset_1 @ (k5_lattice3 @ (k1_lattice3 @ X0) @ X1) @ 
% 0.21/0.50             (u1_struct_0 @ (k1_lattice3 @ X0)))
% 0.21/0.50          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.21/0.50          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(fc2_lattice3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v10_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.21/0.50       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.50  thf('9', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.50  thf(dt_k1_lattice3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.21/0.50       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.50  thf('10', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.21/0.50          | (m1_subset_1 @ (k5_lattice3 @ (k1_lattice3 @ X0) @ X1) @ 
% 0.21/0.50             (u1_struct_0 @ (k1_lattice3 @ X0)))
% 0.21/0.50          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.50  thf(fc1_lattice3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.21/0.50       ( ~( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) ))).
% 0.21/0.50  thf('12', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k5_lattice3 @ (k1_lattice3 @ X0) @ X1) @ 
% 0.21/0.50           (u1_struct_0 @ (k1_lattice3 @ X0)))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0))))),
% 0.21/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((m1_subset_1 @ (k5_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) @ 
% 0.21/0.50        (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.50  thf(d4_lattice3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) =>
% 0.21/0.50           ( ( k5_lattice3 @ A @ B ) = ( B ) ) ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ (k3_lattice3 @ X7)))
% 0.21/0.50          | ((k5_lattice3 @ X7 @ X6) = (X6))
% 0.21/0.50          | ~ (l3_lattices @ X7)
% 0.21/0.50          | ~ (v10_lattices @ X7)
% 0.21/0.50          | (v2_struct_0 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_lattice3])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.21/0.50          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.21/0.50          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | ~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | ((k5_lattice3 @ (k1_lattice3 @ X0) @ X1) = (X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.50  thf('20', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.21/0.50          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.21/0.50          | ((k5_lattice3 @ (k1_lattice3 @ X0) @ X1) = (X1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.50  thf('22', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k5_lattice3 @ (k1_lattice3 @ X0) @ X1) = (X1))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0))))),
% 0.21/0.50      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, (((k5_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k5_lattice3 @ (k1_lattice3 @ X0) @ X1) @ 
% 0.21/0.50           (u1_struct_0 @ (k1_lattice3 @ X0)))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0))))),
% 0.21/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((m1_subset_1 @ (k5_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C) @ 
% 0.21/0.50        (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k5_lattice3 @ (k1_lattice3 @ X0) @ X1) = (X1))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0))))),
% 0.21/0.50      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('31', plain, (((k5_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C) = (sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '31'])).
% 0.21/0.50  thf(t2_lattice3, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.21/0.50           ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C ) <=>
% 0.21/0.50             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ (k1_lattice3 @ X17)))
% 0.21/0.50          | ~ (r1_tarski @ X18 @ X16)
% 0.21/0.50          | (r1_lattices @ (k1_lattice3 @ X17) @ X18 @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ (k1_lattice3 @ X17))))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_lattice3])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.50          | (r1_lattices @ (k1_lattice3 @ sk_A) @ X0 @ sk_C)
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.21/0.50        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.21/0.50         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '24'])).
% 0.21/0.50  thf(redefinition_r3_lattices, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.50         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.50          | ~ (l3_lattices @ X2)
% 0.21/0.50          | ~ (v9_lattices @ X2)
% 0.21/0.50          | ~ (v8_lattices @ X2)
% 0.21/0.50          | ~ (v6_lattices @ X2)
% 0.21/0.50          | (v2_struct_0 @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.50          | (r3_lattices @ X2 @ X1 @ X3)
% 0.21/0.50          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.50          | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.50          | (v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.50          | ~ (v6_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.50          | ~ (v8_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.50          | ~ (v9_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.50          | ~ (l3_lattices @ (k1_lattice3 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf(cc1_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l3_lattices @ A ) =>
% 0.21/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.50           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.50           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v6_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('41', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | (v6_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | ~ (v10_lattices @ (k1_lattice3 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.50  thf('44', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.50  thf('45', plain, (![X0 : $i]: (v6_lattices @ (k1_lattice3 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v8_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('47', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | (v8_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | ~ (v10_lattices @ (k1_lattice3 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('49', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.50  thf('50', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.50  thf('51', plain, (![X0 : $i]: (v8_lattices @ (k1_lattice3 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v9_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('53', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l3_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | (v9_lattices @ (k1_lattice3 @ X0))
% 0.21/0.50          | ~ (v10_lattices @ (k1_lattice3 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.50  thf('56', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.50  thf('57', plain, (![X0 : $i]: (v9_lattices @ (k1_lattice3 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.50  thf('58', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.50          | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.50          | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['39', '45', '51', '57', '58'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      ((((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.50         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.50         | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))
% 0.21/0.50         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '31'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.50         | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))
% 0.21/0.51         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.51  thf('63', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.21/0.51         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.51      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '31'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '24'])).
% 0.21/0.51  thf(t7_lattice3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( r3_lattices @ A @ B @ C ) <=>
% 0.21/0.51                 ( r3_orders_2 @
% 0.21/0.51                   ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ 
% 0.21/0.51                   ( k4_lattice3 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (r3_lattices @ X20 @ X19 @ X21)
% 0.21/0.51          | (r3_orders_2 @ (k3_lattice3 @ X20) @ (k4_lattice3 @ X20 @ X19) @ 
% 0.21/0.51             (k4_lattice3 @ X20 @ X21))
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (l3_lattices @ X20)
% 0.21/0.51          | ~ (v10_lattices @ X20)
% 0.21/0.51          | (v2_struct_0 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_lattice3])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (v10_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (l3_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51          | (r3_orders_2 @ (k3_lattice3 @ (k1_lattice3 @ sk_A)) @ 
% 0.21/0.51             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) @ 
% 0.21/0.51             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ X0))
% 0.21/0.51          | ~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.51  thf('69', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.51  thf('70', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '24'])).
% 0.21/0.51  thf(d3_lattice3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ( k4_lattice3 @ A @ B ) = ( B ) ) ) ) ))).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.51          | ((k4_lattice3 @ X5 @ X4) = (X4))
% 0.21/0.51          | ~ (l3_lattices @ X5)
% 0.21/0.51          | ~ (v10_lattices @ X5)
% 0.21/0.51          | (v2_struct_0 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_lattice3])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ~ (v10_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ~ (l3_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.51  thf('75', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.51  thf('76', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.51  thf('78', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.51  thf('79', plain, (((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51          | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ 
% 0.21/0.51             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ X0))
% 0.21/0.51          | ~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['68', '69', '70', '71', '79'])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      ((~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.21/0.51        | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ 
% 0.21/0.51           (k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C))
% 0.21/0.51        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['65', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '31'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.51          | ((k4_lattice3 @ X5 @ X4) = (X4))
% 0.21/0.51          | ~ (l3_lattices @ X5)
% 0.21/0.51          | ~ (v10_lattices @ X5)
% 0.21/0.51          | (v2_struct_0 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_lattice3])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ~ (v10_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ~ (l3_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C) = (sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('85', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.51  thf('86', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C) = (sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.21/0.51  thf('88', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.51  thf('89', plain, (((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C) = (sk_C))),
% 0.21/0.51      inference('clc', [status(thm)], ['87', '88'])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      ((~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.21/0.51        | (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.21/0.51        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['81', '89'])).
% 0.21/0.51  thf('91', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.21/0.51        | ~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.51      inference('clc', [status(thm)], ['90', '91'])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.21/0.51         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['64', '92'])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      ((~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.21/0.51         <= (~ ((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('95', plain,
% 0.21/0.51      (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)) | 
% 0.21/0.51       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.51  thf('96', plain, (~ ((r1_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['2', '95'])).
% 0.21/0.51  thf('97', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['1', '96'])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '24'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '31'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ (k1_lattice3 @ X17)))
% 0.21/0.51          | ~ (r1_lattices @ (k1_lattice3 @ X17) @ X18 @ X16)
% 0.21/0.51          | (r1_tarski @ X18 @ X16)
% 0.21/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ (k1_lattice3 @ X17))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_lattice3])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51          | (r1_tarski @ X0 @ sk_C)
% 0.21/0.51          | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ X0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      ((~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.21/0.51        | (r1_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['98', '101'])).
% 0.21/0.51  thf('103', plain, (((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_C) = (sk_C))),
% 0.21/0.51      inference('clc', [status(thm)], ['87', '88'])).
% 0.21/0.51  thf('104', plain, (((k4_lattice3 @ (k1_lattice3 @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (r3_orders_2 @ (k3_lattice3 @ X20) @ (k4_lattice3 @ X20 @ X19) @ 
% 0.21/0.51               (k4_lattice3 @ X20 @ X21))
% 0.21/0.51          | (r3_lattices @ X20 @ X19 @ X21)
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (l3_lattices @ X20)
% 0.21/0.51          | ~ (v10_lattices @ X20)
% 0.21/0.51          | (v2_struct_0 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_lattice3])).
% 0.21/0.51  thf('106', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r3_orders_2 @ (k3_lattice3 @ (k1_lattice3 @ sk_A)) @ sk_B @ 
% 0.21/0.51             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ X0))
% 0.21/0.51          | (v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (v10_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (l3_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51          | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (![X22 : $i]: ((k3_yellow_1 @ X22) = (k3_lattice3 @ (k1_lattice3 @ X22)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.51  thf('108', plain, (![X15 : $i]: (v10_lattices @ (k1_lattice3 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.21/0.51  thf('109', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '24'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ 
% 0.21/0.51             (k4_lattice3 @ (k1_lattice3 @ sk_A) @ X0))
% 0.21/0.51          | (v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51          | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 0.21/0.51  thf('112', plain,
% 0.21/0.51      ((~ (r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.21/0.51        | (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['103', '111'])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.21/0.51         <= (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)) | 
% 0.21/0.51       ((r1_tarski @ sk_B @ sk_C))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('115', plain, (((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['2', '95', '114'])).
% 0.21/0.51  thf('116', plain, ((r3_orders_2 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['113', '115'])).
% 0.21/0.51  thf('117', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '31'])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      (((r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.21/0.51        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['112', '116', '117'])).
% 0.21/0.51  thf('119', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.51  thf('120', plain, ((r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['118', '119'])).
% 0.21/0.51  thf('121', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '24'])).
% 0.21/0.51  thf('122', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (l3_lattices @ X2)
% 0.21/0.51          | ~ (v9_lattices @ X2)
% 0.21/0.51          | ~ (v8_lattices @ X2)
% 0.21/0.51          | ~ (v6_lattices @ X2)
% 0.21/0.51          | (v2_struct_0 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.51          | (r1_lattices @ X2 @ X1 @ X3)
% 0.21/0.51          | ~ (r3_lattices @ X2 @ X1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.51  thf('123', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.51          | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51          | (v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (v6_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (v8_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (v9_lattices @ (k1_lattice3 @ sk_A))
% 0.21/0.51          | ~ (l3_lattices @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.51  thf('124', plain, (![X0 : $i]: (v6_lattices @ (k1_lattice3 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.51  thf('125', plain, (![X0 : $i]: (v8_lattices @ (k1_lattice3 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.51  thf('126', plain, (![X0 : $i]: (v9_lattices @ (k1_lattice3 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.51  thf('127', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.21/0.51  thf('128', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r3_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.51          | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51          | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 0.21/0.51  thf('129', plain,
% 0.21/0.51      (((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.21/0.51        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['120', '128'])).
% 0.21/0.51  thf('130', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '31'])).
% 0.21/0.51  thf('131', plain,
% 0.21/0.51      (((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.21/0.51        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['129', '130'])).
% 0.21/0.51  thf('132', plain, (![X12 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.21/0.51  thf('133', plain, ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['131', '132'])).
% 0.21/0.51  thf('134', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['102', '133'])).
% 0.21/0.51  thf('135', plain, ($false), inference('demod', [status(thm)], ['97', '134'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
