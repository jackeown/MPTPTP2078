%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hVqxTFVNtg

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 217 expanded)
%              Number of leaves         :   30 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  937 (3339 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t3_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( r3_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) )
            & ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( r3_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) )
              & ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_waybel_7])).

thf('0',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ~ ( v1_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('2',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r2_yellow_0 @ A @ B )
          & ( r1_yellow_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_yellow_0 @ X10 @ X12 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X6
       != ( k1_yellow_0 @ X4 @ X5 ) )
      | ( r2_lattice3 @ X4 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r1_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ( r2_lattice3 @ X4 @ X5 @ ( k1_yellow_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(t9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ C @ D )
                 => ( r1_lattice3 @ A @ B @ D ) )
                & ( ( r2_lattice3 @ A @ C @ D )
                 => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r2_lattice3 @ X18 @ X17 @ X19 )
      | ( r2_lattice3 @ X18 @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X1 @ ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X1 @ ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_lattice3 @ sk_A @ sk_B @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
       != ( k1_yellow_0 @ X4 @ X5 ) )
      | ~ ( r2_lattice3 @ X4 @ X5 @ X7 )
      | ( r1_orders_2 @ X4 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r1_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ ( k1_yellow_0 @ X4 @ X5 ) @ X7 )
      | ~ ( r2_lattice3 @ X4 @ X5 @ X7 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('41',plain,(
    r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
   <= ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_yellow_0 @ X10 @ X11 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['61','62'])).

thf(t35_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r2_yellow_0 @ A @ B )
            & ( r2_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_orders_2 @ X13 @ ( k2_yellow_0 @ X13 @ X14 ) @ ( k2_yellow_0 @ X13 @ X15 ) )
      | ~ ( r2_yellow_0 @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ~ ( r2_yellow_0 @ X13 @ X15 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( k2_yellow_0 @ sk_A @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( k2_yellow_0 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','68'])).

thf('70',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('71',plain,(
    r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('73',plain,(
    ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['54','73'])).

thf('75',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['52','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['4','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hVqxTFVNtg
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 76 iterations in 0.063s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.21/0.53  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.53  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.21/0.53  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v3_lattice3_type, type, v3_lattice3: $i > $o).
% 0.21/0.53  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.21/0.53  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.21/0.53  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.21/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.53  thf(t3_waybel_7, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.21/0.53         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.21/0.53         ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.53           ( ( r3_orders_2 @
% 0.21/0.53               A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.53             ( r1_orders_2 @
% 0.21/0.53               A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.21/0.53            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.21/0.53            ( l1_orders_2 @ A ) ) =>
% 0.21/0.53          ( ![B:$i,C:$i]:
% 0.21/0.53            ( ( r1_tarski @ B @ C ) =>
% 0.21/0.53              ( ( r3_orders_2 @
% 0.21/0.53                  A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.53                ( r1_orders_2 @
% 0.21/0.53                  A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t3_waybel_7])).
% 0.21/0.53  thf('0', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_lattice3, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_orders_2 @ A ) =>
% 0.21/0.53       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X3 : $i]:
% 0.21/0.53         (~ (v1_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.21/0.53  thf('2', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('3', plain, ((v1_lattice3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('4', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t17_yellow_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.21/0.53         ( v3_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]: ( ( r2_yellow_0 @ A @ B ) & ( r1_yellow_0 @ A @ B ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X10 : $i, X12 : $i]:
% 0.21/0.53         ((r1_yellow_0 @ X10 @ X12)
% 0.21/0.53          | ~ (l1_orders_2 @ X10)
% 0.21/0.53          | ~ (v3_lattice3 @ X10)
% 0.21/0.53          | ~ (v5_orders_2 @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v3_lattice3 @ sk_A)
% 0.21/0.53          | (r1_yellow_0 @ sk_A @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain, ((v3_lattice3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r1_yellow_0 @ sk_A @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.53  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('13', plain, (![X0 : $i]: (r1_yellow_0 @ sk_A @ X0)),
% 0.21/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf(dt_k1_yellow_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( l1_orders_2 @ A ) =>
% 0.21/0.53       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.53  thf(d9_yellow_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_orders_2 @ A ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ( r1_yellow_0 @ A @ B ) =>
% 0.21/0.53             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.21/0.53               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.21/0.53                 ( ![D:$i]:
% 0.21/0.53                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.21/0.53                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         (((X6) != (k1_yellow_0 @ X4 @ X5))
% 0.21/0.53          | (r2_lattice3 @ X4 @ X5 @ X6)
% 0.21/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (r1_yellow_0 @ X4 @ X5)
% 0.21/0.53          | ~ (l1_orders_2 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X4)
% 0.21/0.53          | ~ (r1_yellow_0 @ X4 @ X5)
% 0.21/0.53          | ~ (m1_subset_1 @ (k1_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.21/0.53          | (r2_lattice3 @ X4 @ X5 @ (k1_yellow_0 @ X4 @ X5)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X0)
% 0.21/0.53          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_yellow_0 @ X0 @ X1)
% 0.21/0.53          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | (r2_lattice3 @ sk_A @ X0 @ (k1_yellow_0 @ sk_A @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '18'])).
% 0.21/0.53  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]: (r2_lattice3 @ sk_A @ X0 @ (k1_yellow_0 @ sk_A @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.53  thf(t9_yellow_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_orders_2 @ A ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.53           ( ![D:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.21/0.53                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X16 @ X17)
% 0.21/0.53          | ~ (r2_lattice3 @ X18 @ X17 @ X19)
% 0.21/0.53          | (r2_lattice3 @ X18 @ X16 @ X19)
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.53          | ~ (l1_orders_2 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X0)
% 0.21/0.53          | ~ (l1_orders_2 @ X0)
% 0.21/0.53          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X2 @ X3)
% 0.21/0.53          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | (r2_lattice3 @ sk_A @ X1 @ (k1_yellow_0 @ sk_A @ X0))
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '25'])).
% 0.21/0.53  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_lattice3 @ sk_A @ X1 @ (k1_yellow_0 @ sk_A @ X0))
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ((r2_lattice3 @ sk_A @ sk_B @ (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (((X6) != (k1_yellow_0 @ X4 @ X5))
% 0.21/0.53          | ~ (r2_lattice3 @ X4 @ X5 @ X7)
% 0.21/0.53          | (r1_orders_2 @ X4 @ X6 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (r1_yellow_0 @ X4 @ X5)
% 0.21/0.53          | ~ (l1_orders_2 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X4)
% 0.21/0.53          | ~ (r1_yellow_0 @ X4 @ X5)
% 0.21/0.53          | ~ (m1_subset_1 @ (k1_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.21/0.53          | (r1_orders_2 @ X4 @ (k1_yellow_0 @ X4 @ X5) @ X7)
% 0.21/0.53          | ~ (r2_lattice3 @ X4 @ X5 @ X7))),
% 0.21/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X0)
% 0.21/0.53          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.21/0.53          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_yellow_0 @ X0 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.53          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X0)
% 0.21/0.53          | ~ (l1_orders_2 @ X0)
% 0.21/0.53          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.53             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (r1_yellow_0 @ X0 @ X2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['30', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_yellow_0 @ X0 @ X2)
% 0.21/0.53          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.53             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.53        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.53        | ~ (r1_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '37'])).
% 0.21/0.53  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('40', plain, (![X0 : $i]: (r1_yellow_0 @ sk_A @ X0)),
% 0.21/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53        (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.53  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (l1_orders_2 @ X1)
% 0.21/0.53          | ~ (v3_orders_2 @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.53          | (r3_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.53          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X0)
% 0.21/0.53          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.53          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v3_orders_2 @ X0)
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v3_orders_2 @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.53          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X0)
% 0.21/0.53          | ~ (l1_orders_2 @ X0)
% 0.21/0.53          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.53               (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.53             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v3_orders_2 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v3_orders_2 @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.53             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.53               (k1_yellow_0 @ X0 @ X1))
% 0.21/0.53          | ~ (l1_orders_2 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.53        | (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (v3_orders_2 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['41', '48'])).
% 0.21/0.53  thf('50', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53         (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.53        | ~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.53             (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53           (k1_yellow_0 @ sk_A @ sk_C)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53               (k1_yellow_0 @ sk_A @ sk_C))))),
% 0.21/0.53      inference('split', [status(esa)], ['53'])).
% 0.21/0.53  thf('55', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         ((r2_yellow_0 @ X10 @ X11)
% 0.21/0.53          | ~ (l1_orders_2 @ X10)
% 0.21/0.53          | ~ (v3_lattice3 @ X10)
% 0.21/0.53          | ~ (v5_orders_2 @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v3_lattice3 @ sk_A)
% 0.21/0.53          | (r2_yellow_0 @ sk_A @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.53  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('60', plain, ((v3_lattice3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r2_yellow_0 @ sk_A @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.53  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('63', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.21/0.53      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.53  thf(t35_yellow_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_orders_2 @ A ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( ( r1_tarski @ B @ C ) & ( r2_yellow_0 @ A @ B ) & 
% 0.21/0.53             ( r2_yellow_0 @ A @ C ) ) =>
% 0.21/0.53           ( r1_orders_2 @
% 0.21/0.53             A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ))).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         ((r1_orders_2 @ X13 @ (k2_yellow_0 @ X13 @ X14) @ 
% 0.21/0.53           (k2_yellow_0 @ X13 @ X15))
% 0.21/0.53          | ~ (r2_yellow_0 @ X13 @ X14)
% 0.21/0.53          | ~ (r1_tarski @ X15 @ X14)
% 0.21/0.53          | ~ (r2_yellow_0 @ X13 @ X15)
% 0.21/0.53          | ~ (l1_orders_2 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t35_yellow_0])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (r2_yellow_0 @ sk_A @ X1)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.53          | (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ X0) @ 
% 0.21/0.53             (k2_yellow_0 @ sk_A @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.53  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.21/0.53      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.53          | (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ X0) @ 
% 0.21/0.53             (k2_yellow_0 @ sk_A @ X1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.53        (k2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['55', '68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      ((~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.53           (k2_yellow_0 @ sk_A @ sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.53               (k2_yellow_0 @ sk_A @ sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['53'])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.53         (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (~
% 0.21/0.53       ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53         (k1_yellow_0 @ sk_A @ sk_C))) | 
% 0.21/0.53       ~
% 0.21/0.53       ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.53         (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['53'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (~
% 0.21/0.53       ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53         (k1_yellow_0 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      (~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.53          (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['54', '73'])).
% 0.21/0.53  thf('75', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('clc', [status(thm)], ['52', '74'])).
% 0.21/0.53  thf('76', plain, ($false), inference('demod', [status(thm)], ['4', '75'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
