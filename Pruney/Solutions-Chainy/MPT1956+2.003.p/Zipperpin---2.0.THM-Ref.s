%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3AUDIDgYlc

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 217 expanded)
%              Number of leaves         :   31 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  951 (3345 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

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
    ! [X12: $i,X14: $i] :
      ( ( r1_yellow_0 @ X12 @ X14 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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

thf(t34_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r1_yellow_0 @ A @ B )
            & ( r1_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_orders_2 @ X15 @ ( k1_yellow_0 @ X15 @ X16 ) @ ( k1_yellow_0 @ X15 @ X17 ) )
      | ~ ( r1_yellow_0 @ X15 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_yellow_0 @ X15 @ X16 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X1 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['8','13'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X1 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('33',plain,(
    r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
   <= ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_yellow_0 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
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

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X6
       != ( k2_yellow_0 @ X4 @ X5 ) )
      | ( r1_lattice3 @ X4 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ( r1_lattice3 @ X4 @ X5 @ ( k2_yellow_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

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

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_lattice3 @ X20 @ X19 @ X21 )
      | ( r1_lattice3 @ X20 @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['39','62'])).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X7 @ ( k2_yellow_0 @ X4 @ X5 ) )
      | ~ ( r1_lattice3 @ X4 @ X5 @ X7 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r2_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('75',plain,(
    r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['38','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3AUDIDgYlc
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 76 iterations in 0.031s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.48  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.21/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.48  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.21/0.48  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.21/0.48  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.21/0.48  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.21/0.48  thf(v3_lattice3_type, type, v3_lattice3: $i > $o).
% 0.21/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.48  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.21/0.48  thf(t3_waybel_7, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.21/0.48         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.21/0.48         ( l1_orders_2 @ A ) ) =>
% 0.21/0.48       ( ![B:$i,C:$i]:
% 0.21/0.48         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.48           ( ( r3_orders_2 @
% 0.21/0.48               A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.48             ( r1_orders_2 @
% 0.21/0.48               A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.21/0.48            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.21/0.48            ( l1_orders_2 @ A ) ) =>
% 0.21/0.48          ( ![B:$i,C:$i]:
% 0.21/0.48            ( ( r1_tarski @ B @ C ) =>
% 0.21/0.48              ( ( r3_orders_2 @
% 0.21/0.48                  A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.48                ( r1_orders_2 @
% 0.21/0.48                  A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t3_waybel_7])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.48        | ~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.48             (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.48           (k2_yellow_0 @ sk_A @ sk_B)))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.48               (k2_yellow_0 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t17_yellow_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.21/0.48         ( v3_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]: ( ( r2_yellow_0 @ A @ B ) & ( r1_yellow_0 @ A @ B ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X12 : $i, X14 : $i]:
% 0.21/0.48         ((r1_yellow_0 @ X12 @ X14)
% 0.21/0.48          | ~ (l1_orders_2 @ X12)
% 0.21/0.48          | ~ (v3_lattice3 @ X12)
% 0.21/0.48          | ~ (v5_orders_2 @ X12)
% 0.21/0.48          | (v2_struct_0 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v3_lattice3 @ sk_A)
% 0.21/0.48          | (r1_yellow_0 @ sk_A @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((v3_lattice3 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r1_yellow_0 @ sk_A @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.48  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc1_lattice3, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X3 : $i]:
% 0.21/0.48         (~ (v1_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.21/0.48  thf('11', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, ((v1_lattice3 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, (![X0 : $i]: (r1_yellow_0 @ sk_A @ X0)),
% 0.21/0.48      inference('clc', [status(thm)], ['8', '13'])).
% 0.21/0.48  thf(t34_yellow_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( ![B:$i,C:$i]:
% 0.21/0.48         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 0.21/0.48             ( r1_yellow_0 @ A @ C ) ) =>
% 0.21/0.48           ( r1_orders_2 @
% 0.21/0.48             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         ((r1_orders_2 @ X15 @ (k1_yellow_0 @ X15 @ X16) @ 
% 0.21/0.48           (k1_yellow_0 @ X15 @ X17))
% 0.21/0.48          | ~ (r1_yellow_0 @ X15 @ X17)
% 0.21/0.48          | ~ (r1_tarski @ X16 @ X17)
% 0.21/0.48          | ~ (r1_yellow_0 @ X15 @ X16)
% 0.21/0.48          | ~ (l1_orders_2 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t34_yellow_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ sk_A)
% 0.21/0.48          | ~ (r1_yellow_0 @ sk_A @ X1)
% 0.21/0.48          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.48          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X1) @ 
% 0.21/0.48             (k1_yellow_0 @ sk_A @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain, (![X0 : $i]: (r1_yellow_0 @ sk_A @ X0)),
% 0.21/0.48      inference('clc', [status(thm)], ['8', '13'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.48          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X1) @ 
% 0.21/0.48             (k1_yellow_0 @ sk_A @ X0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '19'])).
% 0.21/0.48  thf(dt_k1_yellow_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X8)
% 0.21/0.48          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X8)
% 0.21/0.48          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.21/0.48  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.48          | ~ (l1_orders_2 @ X1)
% 0.21/0.48          | ~ (v3_orders_2 @ X1)
% 0.21/0.48          | (v2_struct_0 @ X1)
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.48          | (r3_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.48          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X0)
% 0.21/0.48          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.48          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v3_orders_2 @ X0)
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v3_orders_2 @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.48          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.48          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X0)
% 0.21/0.48          | ~ (l1_orders_2 @ X0)
% 0.21/0.48          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.48               (k1_yellow_0 @ X0 @ X1))
% 0.21/0.48          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.48             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (v3_orders_2 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v3_orders_2 @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.48             (k1_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.21/0.48               (k1_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.48        | (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48           (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v3_orders_2 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '27'])).
% 0.21/0.48  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k1_yellow_0 @ sk_A @ sk_C))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.48  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48           (k1_yellow_0 @ sk_A @ sk_C)))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k1_yellow_0 @ sk_A @ sk_C))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k1_yellow_0 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.48         (k2_yellow_0 @ sk_A @ sk_B))) | 
% 0.21/0.48       ~
% 0.21/0.48       ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k1_yellow_0 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.48         (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.48          (k2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 0.21/0.48  thf('39', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((r2_yellow_0 @ X12 @ X13)
% 0.21/0.48          | ~ (l1_orders_2 @ X12)
% 0.21/0.48          | ~ (v3_lattice3 @ X12)
% 0.21/0.48          | ~ (v5_orders_2 @ X12)
% 0.21/0.48          | (v2_struct_0 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v3_lattice3 @ sk_A)
% 0.21/0.48          | (r2_yellow_0 @ sk_A @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('44', plain, ((v3_lattice3 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r2_yellow_0 @ sk_A @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.48  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('47', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.21/0.48      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.48  thf(dt_k2_yellow_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X10)
% 0.21/0.48          | (m1_subset_1 @ (k2_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.21/0.48  thf(d10_yellow_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( ![B:$i,C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ( r2_yellow_0 @ A @ B ) =>
% 0.21/0.48             ( ( ( C ) = ( k2_yellow_0 @ A @ B ) ) <=>
% 0.21/0.48               ( ( r1_lattice3 @ A @ B @ C ) & 
% 0.21/0.48                 ( ![D:$i]:
% 0.21/0.48                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48                     ( ( r1_lattice3 @ A @ B @ D ) =>
% 0.21/0.48                       ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.48         (((X6) != (k2_yellow_0 @ X4 @ X5))
% 0.21/0.48          | (r1_lattice3 @ X4 @ X5 @ X6)
% 0.21/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.48          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.21/0.48          | ~ (l1_orders_2 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X4)
% 0.21/0.48          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.21/0.48          | ~ (m1_subset_1 @ (k2_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.21/0.48          | (r1_lattice3 @ X4 @ X5 @ (k2_yellow_0 @ X4 @ X5)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X0)
% 0.21/0.48          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['48', '50'])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_yellow_0 @ X0 @ X1)
% 0.21/0.48          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ sk_A)
% 0.21/0.48          | (r1_lattice3 @ sk_A @ X0 @ (k2_yellow_0 @ sk_A @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '52'])).
% 0.21/0.48  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (![X0 : $i]: (r1_lattice3 @ sk_A @ X0 @ (k2_yellow_0 @ sk_A @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X10)
% 0.21/0.48          | (m1_subset_1 @ (k2_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.21/0.48  thf(t9_yellow_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( ![B:$i,C:$i]:
% 0.21/0.48         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.48           ( ![D:$i]:
% 0.21/0.48             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.21/0.48                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X18 @ X19)
% 0.21/0.48          | ~ (r1_lattice3 @ X20 @ X19 @ X21)
% 0.21/0.48          | (r1_lattice3 @ X20 @ X18 @ X21)
% 0.21/0.48          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.48          | ~ (l1_orders_2 @ X20))),
% 0.21/0.48      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X0)
% 0.21/0.48          | ~ (l1_orders_2 @ X0)
% 0.21/0.48          | (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (r1_lattice3 @ X0 @ X3 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.48      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X2 @ X3)
% 0.21/0.48          | ~ (r1_lattice3 @ X0 @ X3 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ sk_A)
% 0.21/0.48          | (r1_lattice3 @ sk_A @ X1 @ (k2_yellow_0 @ sk_A @ X0))
% 0.21/0.48          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['55', '59'])).
% 0.21/0.48  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_lattice3 @ sk_A @ X1 @ (k2_yellow_0 @ sk_A @ X0))
% 0.21/0.48          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.48  thf('63', plain, ((r1_lattice3 @ sk_A @ sk_B @ (k2_yellow_0 @ sk_A @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['39', '62'])).
% 0.21/0.48  thf('64', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X10)
% 0.21/0.48          | (m1_subset_1 @ (k2_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.21/0.48  thf('65', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X10)
% 0.21/0.48          | (m1_subset_1 @ (k2_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         (((X6) != (k2_yellow_0 @ X4 @ X5))
% 0.21/0.48          | ~ (r1_lattice3 @ X4 @ X5 @ X7)
% 0.21/0.48          | (r1_orders_2 @ X4 @ X7 @ X6)
% 0.21/0.48          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.21/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.48          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.21/0.48          | ~ (l1_orders_2 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X4)
% 0.21/0.48          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.21/0.48          | ~ (m1_subset_1 @ (k2_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.21/0.48          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.21/0.48          | (r1_orders_2 @ X4 @ X7 @ (k2_yellow_0 @ X4 @ X5))
% 0.21/0.48          | ~ (r1_lattice3 @ X4 @ X5 @ X7))),
% 0.21/0.48      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X0)
% 0.21/0.48          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.21/0.48          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.48          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['65', '67'])).
% 0.21/0.48  thf('69', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_yellow_0 @ X0 @ X1)
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.48          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.48  thf('70', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X0)
% 0.21/0.48          | ~ (l1_orders_2 @ X0)
% 0.21/0.48          | ~ (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | (r1_orders_2 @ X0 @ (k2_yellow_0 @ X0 @ X1) @ 
% 0.21/0.48             (k2_yellow_0 @ X0 @ X2))
% 0.21/0.48          | ~ (r2_yellow_0 @ X0 @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['64', '69'])).
% 0.21/0.48  thf('71', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_yellow_0 @ X0 @ X2)
% 0.21/0.48          | (r1_orders_2 @ X0 @ (k2_yellow_0 @ X0 @ X1) @ 
% 0.21/0.48             (k2_yellow_0 @ X0 @ X2))
% 0.21/0.48          | ~ (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.21/0.48          | ~ (l1_orders_2 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.48  thf('72', plain,
% 0.21/0.48      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.48        | (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.48           (k2_yellow_0 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (r2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['63', '71'])).
% 0.21/0.48  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('74', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.21/0.48      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.48  thf('75', plain,
% 0.21/0.48      ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.21/0.48        (k2_yellow_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.21/0.48  thf('76', plain, ($false), inference('demod', [status(thm)], ['38', '75'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
