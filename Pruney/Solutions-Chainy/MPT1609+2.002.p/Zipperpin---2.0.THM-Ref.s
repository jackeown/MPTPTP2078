%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mtwYwX0egJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 360 expanded)
%              Number of leaves         :   47 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          : 1170 (3458 expanded)
%              Number of equality atoms :   66 ( 312 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(t17_yellow_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
         => ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
              = ( k2_xboole_0 @ B @ C ) )
            & ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
              = ( k3_xboole_0 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
           => ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
                = ( k2_xboole_0 @ B @ C ) )
              & ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
                = ( k3_xboole_0 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_yellow_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(l19_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
         => ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) )
            & ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X27 @ X25 ) @ ( k9_setfam_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[l19_yellow_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ X26 ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X27 @ X25 ) @ ( k9_setfam_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X0 @ sk_B_1 ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) )
      | ( r2_hidden @ ( k3_xboole_0 @ X27 @ X25 ) @ ( k9_setfam_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[l19_yellow_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ X26 ) )
      | ( r2_hidden @ ( k3_xboole_0 @ X27 @ X25 ) @ ( k9_setfam_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_B_1 @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf(t9_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ A )
               => ( ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C )
                  = ( k3_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) ) )
      | ~ ( r2_hidden @ ( k3_xboole_0 @ X34 @ X36 ) @ X35 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X35 ) @ X34 @ X36 )
        = ( k3_xboole_0 @ X34 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) ) )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_1])).

thf('25',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('26',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('27',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ~ ( r2_hidden @ ( k3_xboole_0 @ X34 @ X36 ) @ X35 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X35 ) @ X34 @ X36 )
        = ( k3_xboole_0 @ X34 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k11_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 @ sk_C )
      = ( k3_xboole_0 @ sk_B_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( ( k12_lattice3 @ X12 @ X11 @ X13 )
        = ( k11_lattice3 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('37',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X24: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('40',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(fc1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( v1_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v3_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v4_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v5_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v1_lattice3 @ ( k3_lattice3 @ A ) )
        & ( v2_lattice3 @ ( k3_lattice3 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X20: $i] :
      ( ( v2_lattice3 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(fc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( v10_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('43',plain,(
    ! [X10: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf(dt_k1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('44',plain,(
    ! [X6: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(fc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( v3_lattices @ ( k1_lattice3 @ A ) )
      & ~ ( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) )).

thf('46',plain,(
    ! [X7: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('47',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','39','47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','51'])).

thf('53',plain,
    ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29','30','53','54'])).

thf('56',plain,
    ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
    | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ X26 ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X27 @ X25 ) @ ( k9_setfam_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X0 @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_B_1 @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf(t8_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ A )
               => ( ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C )
                  = ( k2_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) ) )
      | ~ ( r2_hidden @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X32 ) @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_yellow_1])).

thf('64',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('65',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('66',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X32 ) @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k10_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 @ sk_C )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('69',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('71',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('73',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v1_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( ( k13_lattice3 @ X15 @ X14 @ X16 )
        = ( k10_lattice3 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('76',plain,(
    ! [X0: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('77',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('78',plain,(
    ! [X20: $i] :
      ( ( v1_lattice3 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X10: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('81',plain,(
    ! [X6: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X7: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('84',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','86'])).

thf('88',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68','69','88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('92',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['56'])).

thf('94',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) )
    | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['56'])).

thf('97',plain,(
    ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['95','96'])).

thf('98',plain,(
    ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['57','97'])).

thf('99',plain,(
    v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['55','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['13','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mtwYwX0egJ
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 100 iterations in 0.025s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.50  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.50  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.50  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.50  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.50  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.20/0.50  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.50  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.20/0.50  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.50  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.20/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.50  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.20/0.50  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.50  thf(t17_yellow_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.50           ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.50               ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.50             ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.50               ( k3_xboole_0 @ B @ C ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.50          ( ![C:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.50              ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.50                  ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.50                ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.50                  ( k3_xboole_0 @ B @ C ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t17_yellow_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t4_yellow_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k2_yellow_1 @ (k9_setfam_1 @ X30)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.50  thf(t1_yellow_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.50       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.50  thf('2', plain, (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('5', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf(l19_yellow_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.50           ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) & 
% 0.20/0.50             ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k3_yellow_1 @ X26)))
% 0.20/0.50          | (r2_hidden @ (k2_xboole_0 @ X27 @ X25) @ (k9_setfam_1 @ X26))
% 0.20/0.50          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k3_yellow_1 @ X26))))),
% 0.20/0.50      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X25 @ (k9_setfam_1 @ X26))
% 0.20/0.50          | (r2_hidden @ (k2_xboole_0 @ X27 @ X25) @ (k9_setfam_1 @ X26))
% 0.20/0.50          | ~ (m1_subset_1 @ X27 @ (k9_setfam_1 @ X26)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50          | (r2_hidden @ (k2_xboole_0 @ X0 @ sk_B_1) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((r2_hidden @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '10'])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('13', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('17', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k3_yellow_1 @ X26)))
% 0.20/0.50          | (r2_hidden @ (k3_xboole_0 @ X27 @ X25) @ (k9_setfam_1 @ X26))
% 0.20/0.50          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k3_yellow_1 @ X26))))),
% 0.20/0.50      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X25 @ (k9_setfam_1 @ X26))
% 0.20/0.50          | (r2_hidden @ (k3_xboole_0 @ X27 @ X25) @ (k9_setfam_1 @ X26))
% 0.20/0.50          | ~ (m1_subset_1 @ X27 @ (k9_setfam_1 @ X26)))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50          | (r2_hidden @ (k3_xboole_0 @ X0 @ sk_C) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((r2_hidden @ (k3_xboole_0 @ sk_B_1 @ sk_C) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '22'])).
% 0.20/0.50  thf(t9_yellow_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.50               ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ A ) =>
% 0.20/0.50                 ( ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.50                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ (k2_yellow_1 @ X35)))
% 0.20/0.50          | ~ (r2_hidden @ (k3_xboole_0 @ X34 @ X36) @ X35)
% 0.20/0.50          | ((k11_lattice3 @ (k2_yellow_1 @ X35) @ X34 @ X36)
% 0.20/0.50              = (k3_xboole_0 @ X34 @ X36))
% 0.20/0.50          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ (k2_yellow_1 @ X35)))
% 0.20/0.50          | (v1_xboole_0 @ X35))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_yellow_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X34 @ X35)
% 0.20/0.50          | ~ (r2_hidden @ (k3_xboole_0 @ X34 @ X36) @ X35)
% 0.20/0.50          | ((k11_lattice3 @ (k2_yellow_1 @ X35) @ X34 @ X36)
% 0.20/0.50              = (k3_xboole_0 @ X34 @ X36))
% 0.20/0.50          | ~ (m1_subset_1 @ X36 @ X35)
% 0.20/0.50          | (v1_xboole_0 @ X35))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50        | ~ (m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))
% 0.20/0.50        | ((k11_lattice3 @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1 @ sk_C)
% 0.20/0.50            = (k3_xboole_0 @ sk_B_1 @ sk_C))
% 0.20/0.50        | ~ (m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '27'])).
% 0.20/0.50  thf('29', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k2_yellow_1 @ (k9_setfam_1 @ X30)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.50  thf('31', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('32', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(redefinition_k12_lattice3, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.20/0.50          | ~ (l1_orders_2 @ X12)
% 0.20/0.50          | ~ (v2_lattice3 @ X12)
% 0.20/0.50          | ~ (v5_orders_2 @ X12)
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.50          | ((k12_lattice3 @ X12 @ X11 @ X13)
% 0.20/0.50              = (k11_lattice3 @ X12 @ X11 @ X13)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.50          | ((k12_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.50              = (k11_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.50          | ~ (v5_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.50          | ~ (v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.50          | ~ (l1_orders_2 @ (k3_yellow_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k2_yellow_1 @ (k9_setfam_1 @ X30)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.50  thf(fc5_yellow_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.50       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.50       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.50       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.50  thf('38', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.50  thf('39', plain, (![X0 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf(d2_yellow_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.50  thf(fc1_yellow_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.50         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.50         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.50         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.50         ( v1_lattice3 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.50         ( v2_lattice3 @ ( k3_lattice3 @ A ) ) ) ))).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X20 : $i]:
% 0.20/0.50         ((v2_lattice3 @ (k3_lattice3 @ X20))
% 0.20/0.50          | ~ (l3_lattices @ X20)
% 0.20/0.50          | ~ (v10_lattices @ X20)
% 0.20/0.50          | (v2_struct_0 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_yellow_1])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.50          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.20/0.50          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.20/0.50          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf(fc2_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v10_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.50       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.50  thf('43', plain, (![X10 : $i]: (v10_lattices @ (k1_lattice3 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.20/0.50  thf(dt_k1_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.50       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.50  thf('44', plain, (![X6 : $i]: (l3_lattices @ (k1_lattice3 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.50          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.50  thf(fc1_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.50       ( ~( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) ))).
% 0.20/0.50  thf('46', plain, (![X7 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.50  thf('47', plain, (![X0 : $i]: (v2_lattice3 @ (k3_yellow_1 @ X0))),
% 0.20/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k2_yellow_1 @ (k9_setfam_1 @ X30)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.50  thf(dt_k2_yellow_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.50       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.50  thf('49', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.50  thf('50', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.50          | ((k12_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.50              = (k11_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k9_setfam_1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36', '39', '47', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50          | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)
% 0.20/0.50              = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50         = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '52'])).
% 0.20/0.50  thf('54', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50        | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50            = (k3_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29', '30', '53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50          != (k2_xboole_0 @ sk_B_1 @ sk_C))
% 0.20/0.50        | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50            != (k3_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50          != (k3_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50                = (k3_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['56'])).
% 0.20/0.50  thf('58', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('59', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X25 @ (k9_setfam_1 @ X26))
% 0.20/0.50          | (r2_hidden @ (k2_xboole_0 @ X27 @ X25) @ (k9_setfam_1 @ X26))
% 0.20/0.50          | ~ (m1_subset_1 @ X27 @ (k9_setfam_1 @ X26)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50          | (r2_hidden @ (k2_xboole_0 @ X0 @ sk_C) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      ((r2_hidden @ (k2_xboole_0 @ sk_B_1 @ sk_C) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '61'])).
% 0.20/0.50  thf(t8_yellow_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.50               ( ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ A ) =>
% 0.20/0.50                 ( ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.50                   ( k2_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ (k2_yellow_1 @ X32)))
% 0.20/0.50          | ~ (r2_hidden @ (k2_xboole_0 @ X31 @ X33) @ X32)
% 0.20/0.50          | ((k10_lattice3 @ (k2_yellow_1 @ X32) @ X31 @ X33)
% 0.20/0.50              = (k2_xboole_0 @ X31 @ X33))
% 0.20/0.50          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ (k2_yellow_1 @ X32)))
% 0.20/0.50          | (v1_xboole_0 @ X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [t8_yellow_1])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X31 @ X32)
% 0.20/0.50          | ~ (r2_hidden @ (k2_xboole_0 @ X31 @ X33) @ X32)
% 0.20/0.50          | ((k10_lattice3 @ (k2_yellow_1 @ X32) @ X31 @ X33)
% 0.20/0.50              = (k2_xboole_0 @ X31 @ X33))
% 0.20/0.50          | ~ (m1_subset_1 @ X33 @ X32)
% 0.20/0.50          | (v1_xboole_0 @ X32))),
% 0.20/0.50      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50        | ~ (m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))
% 0.20/0.50        | ((k10_lattice3 @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1 @ sk_C)
% 0.20/0.50            = (k2_xboole_0 @ sk_B_1 @ sk_C))
% 0.20/0.50        | ~ (m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['62', '66'])).
% 0.20/0.50  thf('68', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k2_yellow_1 @ (k9_setfam_1 @ X30)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.50  thf('70', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('71', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(redefinition_k13_lattice3, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ~ (l1_orders_2 @ X15)
% 0.20/0.50          | ~ (v1_lattice3 @ X15)
% 0.20/0.50          | ~ (v5_orders_2 @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ((k13_lattice3 @ X15 @ X14 @ X16)
% 0.20/0.50              = (k10_lattice3 @ X15 @ X14 @ X16)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.50          | ((k13_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.50              = (k10_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.50          | ~ (v5_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.50          | ~ (v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.50          | ~ (l1_orders_2 @ (k3_yellow_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('76', plain, (![X0 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (![X20 : $i]:
% 0.20/0.50         ((v1_lattice3 @ (k3_lattice3 @ X20))
% 0.20/0.50          | ~ (l3_lattices @ X20)
% 0.20/0.50          | ~ (v10_lattices @ X20)
% 0.20/0.50          | (v2_struct_0 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_yellow_1])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.50          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.20/0.50          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.20/0.50          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['77', '78'])).
% 0.20/0.50  thf('80', plain, (![X10 : $i]: (v10_lattices @ (k1_lattice3 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.20/0.50  thf('81', plain, (![X6 : $i]: (l3_lattices @ (k1_lattice3 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.50          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.20/0.50  thf('83', plain, (![X7 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.50  thf('84', plain, (![X0 : $i]: (v1_lattice3 @ (k3_yellow_1 @ X0))),
% 0.20/0.50      inference('clc', [status(thm)], ['82', '83'])).
% 0.20/0.50  thf('85', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.50          | ((k13_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.50              = (k10_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k9_setfam_1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['74', '75', '76', '84', '85'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50          | ((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)
% 0.20/0.50              = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['71', '86'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50         = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['70', '87'])).
% 0.20/0.50  thf('89', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.50        | ((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50            = (k2_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['67', '68', '69', '88', '89'])).
% 0.20/0.50  thf('91', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50         = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50          != (k2_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50                = (k2_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['56'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      ((((k2_xboole_0 @ sk_B_1 @ sk_C) != (k2_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.50         <= (~
% 0.20/0.50             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50                = (k2_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50          = (k2_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['94'])).
% 0.20/0.50  thf('96', plain,
% 0.20/0.50      (~
% 0.20/0.50       (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50          = (k3_xboole_0 @ sk_B_1 @ sk_C))) | 
% 0.20/0.50       ~
% 0.20/0.50       (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50          = (k2_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['56'])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      (~
% 0.20/0.50       (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50          = (k3_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['95', '96'])).
% 0.20/0.50  thf('98', plain,
% 0.20/0.50      (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.50         != (k3_xboole_0 @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['57', '97'])).
% 0.20/0.50  thf('99', plain, ((v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['55', '98'])).
% 0.20/0.50  thf('100', plain, ($false), inference('demod', [status(thm)], ['13', '99'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
