%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8UsJxKkpJl

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 249 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          : 1248 (3861 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_yellow_0 @ X16 @ X18 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v3_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ~ ( v1_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('11',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['8','13'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
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

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X10
       != ( k1_yellow_0 @ X8 @ X9 ) )
      | ( r2_lattice3 @ X8 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_yellow_0 @ X8 @ X9 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( r1_yellow_0 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) )
      | ( r2_lattice3 @ X8 @ X9 @ ( k1_yellow_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
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

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r2_lattice3 @ X21 @ X20 @ X22 )
      | ( r2_lattice3 @ X21 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X1 @ ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X1 @ ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r2_lattice3 @ sk_A @ sk_B @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','29'])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k1_yellow_0 @ X8 @ X9 ) )
      | ~ ( r2_lattice3 @ X8 @ X9 @ X11 )
      | ( r1_orders_2 @ X8 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_yellow_0 @ X8 @ X9 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( r1_yellow_0 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ ( k1_yellow_0 @ X8 @ X9 ) @ X11 )
      | ~ ( r2_lattice3 @ X8 @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['8','13'])).

thf('42',plain,(
    r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
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

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('55',plain,(
    r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
   <= ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('61',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_yellow_0 @ X16 @ X17 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v3_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(d10_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_yellow_0 @ A @ B )
           => ( ( C
                = ( k2_yellow_0 @ A @ B ) )
            <=> ( ( r1_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X6
       != ( k2_yellow_0 @ X4 @ X5 ) )
      | ( r1_lattice3 @ X4 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('72',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ( r1_lattice3 @ X4 @ X5 @ ( k2_yellow_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_lattice3 @ X21 @ X20 @ X22 )
      | ( r1_lattice3 @ X21 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['61','84'])).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('87',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('88',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
       != ( k2_yellow_0 @ X4 @ X5 ) )
      | ~ ( r1_lattice3 @ X4 @ X5 @ X7 )
      | ( r1_orders_2 @ X4 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('89',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X7 @ ( k2_yellow_0 @ X4 @ X5 ) )
      | ~ ( r1_lattice3 @ X4 @ X5 @ X7 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r2_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('97',plain,(
    r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['60','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8UsJxKkpJl
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:42:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 88 iterations in 0.054s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.52  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.52  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.21/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.52  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.21/0.52  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.21/0.52  thf(v3_lattice3_type, type, v3_lattice3: $i > $o).
% 0.21/0.52  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.21/0.52  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.21/0.52  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.21/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(t3_waybel_7, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.21/0.52         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.21/0.52         ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i,C:$i]:
% 0.21/0.52         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.52           ( ( r3_orders_2 @
% 0.21/0.52               A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.52             ( r1_orders_2 @
% 0.21/0.52               A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.21/0.52            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.21/0.52            ( l1_orders_2 @ A ) ) =>
% 0.21/0.52          ( ![B:$i,C:$i]:
% 0.21/0.52            ( ( r1_tarski @ B @ C ) =>
% 0.21/0.52              ( ( r3_orders_2 @
% 0.21/0.52                  A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.52                ( r1_orders_2 @
% 0.21/0.52                  A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t3_waybel_7])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.52        | ~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.52             (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.52           (k2_yellow_0 @ sk_A @ sk_B)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.52               (k2_yellow_0 @ sk_A @ sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('3', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t17_yellow_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.21/0.52         ( v3_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]: ( ( r2_yellow_0 @ A @ B ) & ( r1_yellow_0 @ A @ B ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X16 : $i, X18 : $i]:
% 0.21/0.52         ((r1_yellow_0 @ X16 @ X18)
% 0.21/0.52          | ~ (l1_orders_2 @ X16)
% 0.21/0.52          | ~ (v3_lattice3 @ X16)
% 0.21/0.52          | ~ (v5_orders_2 @ X16)
% 0.21/0.52          | (v2_struct_0 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v3_lattice3 @ sk_A)
% 0.21/0.52          | (r1_yellow_0 @ sk_A @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain, ((v3_lattice3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r1_yellow_0 @ sk_A @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.52  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_lattice3, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_orders_2 @ A ) =>
% 0.21/0.52       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X3 : $i]:
% 0.21/0.52         (~ (v1_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.21/0.52  thf('11', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, ((v1_lattice3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain, (![X0 : $i]: (r1_yellow_0 @ sk_A @ X0)),
% 0.21/0.52      inference('clc', [status(thm)], ['8', '13'])).
% 0.21/0.52  thf(dt_k1_yellow_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( l1_orders_2 @ A ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X12)
% 0.21/0.52          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.52  thf(d9_yellow_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_orders_2 @ A ) =>
% 0.21/0.52       ( ![B:$i,C:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( ( r1_yellow_0 @ A @ B ) =>
% 0.21/0.52             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.21/0.52               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.21/0.52                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         (((X10) != (k1_yellow_0 @ X8 @ X9))
% 0.21/0.52          | (r2_lattice3 @ X8 @ X9 @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.52          | ~ (r1_yellow_0 @ X8 @ X9)
% 0.21/0.52          | ~ (l1_orders_2 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X8)
% 0.21/0.52          | ~ (r1_yellow_0 @ X8 @ X9)
% 0.21/0.52          | ~ (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8))
% 0.21/0.52          | (r2_lattice3 @ X8 @ X9 @ (k1_yellow_0 @ X8 @ X9)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_yellow_0 @ X0 @ X1)
% 0.21/0.52          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | (r2_lattice3 @ sk_A @ X0 @ (k1_yellow_0 @ sk_A @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.52  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i]: (r2_lattice3 @ sk_A @ X0 @ (k1_yellow_0 @ sk_A @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X12)
% 0.21/0.52          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.52  thf(t9_yellow_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_orders_2 @ A ) =>
% 0.21/0.52       ( ![B:$i,C:$i]:
% 0.21/0.52         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.52           ( ![D:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.21/0.52                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X19 @ X20)
% 0.21/0.52          | ~ (r2_lattice3 @ X21 @ X20 @ X22)
% 0.21/0.52          | (r2_lattice3 @ X21 @ X19 @ X22)
% 0.21/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (l1_orders_2 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (l1_orders_2 @ X0)
% 0.21/0.52          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X2 @ X3)
% 0.21/0.52          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | (r2_lattice3 @ sk_A @ X1 @ (k1_yellow_0 @ sk_A @ X0))
% 0.21/0.52          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '26'])).
% 0.21/0.52  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_lattice3 @ sk_A @ X1 @ (k1_yellow_0 @ sk_A @ X0))
% 0.21/0.52          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain, ((r2_lattice3 @ sk_A @ sk_B @ (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X12)
% 0.21/0.52          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X12)
% 0.21/0.52          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (((X10) != (k1_yellow_0 @ X8 @ X9))
% 0.21/0.52          | ~ (r2_lattice3 @ X8 @ X9 @ X11)
% 0.21/0.52          | (r1_orders_2 @ X8 @ X10 @ X11)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.21/0.52          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.52          | ~ (r1_yellow_0 @ X8 @ X9)
% 0.21/0.52          | ~ (l1_orders_2 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X8)
% 0.21/0.52          | ~ (r1_yellow_0 @ X8 @ X9)
% 0.21/0.52          | ~ (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8))
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 0.21/0.52          | (r1_orders_2 @ X8 @ (k1_yellow_0 @ X8 @ X9) @ X11)
% 0.21/0.52          | ~ (r2_lattice3 @ X8 @ X9 @ X11))),
% 0.21/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.21/0.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_yellow_0 @ X0 @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.52          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.52             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r1_yellow_0 @ X0 @ X2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_yellow_0 @ X0 @ X2)
% 0.21/0.52          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.52             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.52        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.52        | ~ (r1_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '38'])).
% 0.21/0.52  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain, (![X0 : $i]: (r1_yellow_0 @ sk_A @ X0)),
% 0.21/0.52      inference('clc', [status(thm)], ['8', '13'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52        (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X12)
% 0.21/0.52          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X12)
% 0.21/0.52          | (m1_subset_1 @ (k1_yellow_0 @ X12 @ X13) @ (u1_struct_0 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.52  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (l1_orders_2 @ X1)
% 0.21/0.52          | ~ (v3_orders_2 @ X1)
% 0.21/0.52          | (v2_struct_0 @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.52          | (r3_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.52          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.52          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v3_orders_2 @ X0)
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v3_orders_2 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.52          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.52               (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.52             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v3_orders_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v3_orders_2 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.52             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.52               (k1_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.52        | (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v3_orders_2 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '49'])).
% 0.21/0.52  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('52', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52         (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.52  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52        (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.52      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52           (k1_yellow_0 @ sk_A @ sk_C)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52               (k1_yellow_0 @ sk_A @ sk_C))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52         (k1_yellow_0 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (~
% 0.21/0.52       ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.52         (k2_yellow_0 @ sk_A @ sk_B))) | 
% 0.21/0.52       ~
% 0.21/0.52       ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.52         (k1_yellow_0 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (~
% 0.21/0.52       ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.52         (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.52          (k2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 0.21/0.52  thf('61', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         ((r2_yellow_0 @ X16 @ X17)
% 0.21/0.52          | ~ (l1_orders_2 @ X16)
% 0.21/0.52          | ~ (v3_lattice3 @ X16)
% 0.21/0.52          | ~ (v5_orders_2 @ X16)
% 0.21/0.52          | (v2_struct_0 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v3_lattice3 @ sk_A)
% 0.21/0.52          | (r2_yellow_0 @ sk_A @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('65', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('66', plain, ((v3_lattice3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r2_yellow_0 @ sk_A @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.52  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('69', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.21/0.52      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.52  thf(dt_k2_yellow_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( l1_orders_2 @ A ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X14)
% 0.21/0.52          | (m1_subset_1 @ (k2_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.21/0.52  thf(d10_yellow_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_orders_2 @ A ) =>
% 0.21/0.52       ( ![B:$i,C:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( ( r2_yellow_0 @ A @ B ) =>
% 0.21/0.52             ( ( ( C ) = ( k2_yellow_0 @ A @ B ) ) <=>
% 0.21/0.52               ( ( r1_lattice3 @ A @ B @ C ) & 
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                     ( ( r1_lattice3 @ A @ B @ D ) =>
% 0.21/0.52                       ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (((X6) != (k2_yellow_0 @ X4 @ X5))
% 0.21/0.52          | (r1_lattice3 @ X4 @ X5 @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.52          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.21/0.52          | ~ (l1_orders_2 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X4)
% 0.21/0.52          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.21/0.52          | ~ (m1_subset_1 @ (k2_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.21/0.52          | (r1_lattice3 @ X4 @ X5 @ (k2_yellow_0 @ X4 @ X5)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['70', '72'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_yellow_0 @ X0 @ X1)
% 0.21/0.52          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | (r1_lattice3 @ sk_A @ X0 @ (k2_yellow_0 @ sk_A @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['69', '74'])).
% 0.21/0.52  thf('76', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (![X0 : $i]: (r1_lattice3 @ sk_A @ X0 @ (k2_yellow_0 @ sk_A @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X14)
% 0.21/0.52          | (m1_subset_1 @ (k2_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X19 @ X20)
% 0.21/0.52          | ~ (r1_lattice3 @ X21 @ X20 @ X22)
% 0.21/0.52          | (r1_lattice3 @ X21 @ X19 @ X22)
% 0.21/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (l1_orders_2 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (l1_orders_2 @ X0)
% 0.21/0.52          | (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r1_lattice3 @ X0 @ X3 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X2 @ X3)
% 0.21/0.52          | ~ (r1_lattice3 @ X0 @ X3 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['80'])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | (r1_lattice3 @ sk_A @ X1 @ (k2_yellow_0 @ sk_A @ X0))
% 0.21/0.52          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['77', '81'])).
% 0.21/0.52  thf('83', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_lattice3 @ sk_A @ X1 @ (k2_yellow_0 @ sk_A @ X0))
% 0.21/0.52          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('85', plain, ((r1_lattice3 @ sk_A @ sk_B @ (k2_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['61', '84'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X14)
% 0.21/0.52          | (m1_subset_1 @ (k2_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X14)
% 0.21/0.52          | (m1_subset_1 @ (k2_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (((X6) != (k2_yellow_0 @ X4 @ X5))
% 0.21/0.52          | ~ (r1_lattice3 @ X4 @ X5 @ X7)
% 0.21/0.52          | (r1_orders_2 @ X4 @ X7 @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.21/0.52          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.52          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.21/0.52          | ~ (l1_orders_2 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X4)
% 0.21/0.52          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.21/0.52          | ~ (m1_subset_1 @ (k2_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.21/0.52          | (r1_orders_2 @ X4 @ X7 @ (k2_yellow_0 @ X4 @ X5))
% 0.21/0.52          | ~ (r1_lattice3 @ X4 @ X5 @ X7))),
% 0.21/0.52      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.21/0.52          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['87', '89'])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_yellow_0 @ X0 @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['90'])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (l1_orders_2 @ X0)
% 0.21/0.52          | ~ (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | (r1_orders_2 @ X0 @ (k2_yellow_0 @ X0 @ X1) @ 
% 0.21/0.52             (k2_yellow_0 @ X0 @ X2))
% 0.21/0.52          | ~ (r2_yellow_0 @ X0 @ X2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['86', '91'])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_yellow_0 @ X0 @ X2)
% 0.21/0.52          | (r1_orders_2 @ X0 @ (k2_yellow_0 @ X0 @ X1) @ 
% 0.21/0.52             (k2_yellow_0 @ X0 @ X2))
% 0.21/0.52          | ~ (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.52          | ~ (l1_orders_2 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['92'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.52        | (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.52           (k2_yellow_0 @ sk_A @ sk_B))
% 0.21/0.52        | ~ (r2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['85', '93'])).
% 0.21/0.52  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('96', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.21/0.52      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.52        (k2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.21/0.52  thf('98', plain, ($false), inference('demod', [status(thm)], ['60', '97'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
