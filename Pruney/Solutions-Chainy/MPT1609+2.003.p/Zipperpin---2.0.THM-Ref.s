%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8zZgKfWBW3

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 348 expanded)
%              Number of leaves         :   47 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          : 1155 (3404 expanded)
%              Number of equality atoms :   64 ( 304 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

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
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ ( k3_yellow_1 @ X27 ) ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X28 @ X26 ) @ ( k9_setfam_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_yellow_1 @ X27 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k9_setfam_1 @ X27 ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X28 @ X26 ) @ ( k9_setfam_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ X27 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ ( k3_yellow_1 @ X27 ) ) )
      | ( r2_hidden @ ( k3_xboole_0 @ X28 @ X26 ) @ ( k9_setfam_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_yellow_1 @ X27 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k9_setfam_1 @ X27 ) )
      | ( r2_hidden @ ( k3_xboole_0 @ X28 @ X26 ) @ ( k9_setfam_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ X27 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) ) )
      | ~ ( r2_hidden @ ( k3_xboole_0 @ X35 @ X37 ) @ X36 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X36 ) @ X35 @ X37 )
        = ( k3_xboole_0 @ X35 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) ) )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_1])).

thf('25',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('26',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('27',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ~ ( r2_hidden @ ( k3_xboole_0 @ X35 @ X37 ) @ X36 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X36 ) @ X35 @ X37 )
        = ( k3_xboole_0 @ X35 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
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
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X31 ) ) ) ),
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

thf(fc7_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ~ ( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X25: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('38',plain,(
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

thf('39',plain,(
    ! [X20: $i] :
      ( ( v2_lattice3 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(fc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( v10_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('41',plain,(
    ! [X10: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf(dt_k1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('42',plain,(
    ! [X6: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(fc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( v3_lattices @ ( k1_lattice3 @ A ) )
      & ~ ( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) )).

thf('44',plain,(
    ! [X7: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('45',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(dt_k3_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,
    ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29','30','49','50'])).

thf('52',plain,
    ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
    | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k9_setfam_1 @ X27 ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X28 @ X26 ) @ ( k9_setfam_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X0 @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_B_1 @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

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

thf('59',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) ) )
      | ~ ( r2_hidden @ ( k2_xboole_0 @ X32 @ X34 ) @ X33 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X33 ) @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) ) )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_yellow_1])).

thf('60',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('61',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('62',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ~ ( r2_hidden @ ( k2_xboole_0 @ X32 @ X34 ) @ X33 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X33 ) @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k10_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 @ sk_C )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('65',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('67',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v1_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( ( k13_lattice3 @ X15 @ X14 @ X16 )
        = ( k10_lattice3 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('72',plain,(
    ! [X25: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('73',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('74',plain,(
    ! [X20: $i] :
      ( ( v1_lattice3 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X10: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('77',plain,(
    ! [X6: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X7: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('80',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','82'])).

thf('84',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65','84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('88',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['52'])).

thf('90',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k3_xboole_0 @ sk_B_1 @ sk_C ) )
    | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
     != ( k2_xboole_0 @ sk_B_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['52'])).

thf('93',plain,(
    ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k3_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['53','93'])).

thf('95',plain,(
    v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['51','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['13','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8zZgKfWBW3
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 93 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.49  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.49  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.49  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.20/0.49  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.49  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.49  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.49  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.49  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.49  thf(t17_yellow_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49               ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.49             ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49               ( k3_xboole_0 @ B @ C ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49          ( ![C:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49              ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49                  ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.49                ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49                  ( k3_xboole_0 @ B @ C ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t17_yellow_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t4_yellow_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k2_yellow_1 @ (k9_setfam_1 @ X31)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf(t1_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.49       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.49  thf('2', plain, (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('5', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf(l19_yellow_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) & 
% 0.20/0.49             ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ (k3_yellow_1 @ X27)))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X28 @ X26) @ (k9_setfam_1 @ X27))
% 0.20/0.49          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k3_yellow_1 @ X27))))),
% 0.20/0.49      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X26 @ (k9_setfam_1 @ X27))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X28 @ X26) @ (k9_setfam_1 @ X27))
% 0.20/0.49          | ~ (m1_subset_1 @ X28 @ (k9_setfam_1 @ X27)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X0 @ sk_B_1) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((r2_hidden @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '10'])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('13', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('17', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ (k3_yellow_1 @ X27)))
% 0.20/0.49          | (r2_hidden @ (k3_xboole_0 @ X28 @ X26) @ (k9_setfam_1 @ X27))
% 0.20/0.49          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k3_yellow_1 @ X27))))),
% 0.20/0.49      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X26 @ (k9_setfam_1 @ X27))
% 0.20/0.49          | (r2_hidden @ (k3_xboole_0 @ X28 @ X26) @ (k9_setfam_1 @ X27))
% 0.20/0.49          | ~ (m1_subset_1 @ X28 @ (k9_setfam_1 @ X27)))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | (r2_hidden @ (k3_xboole_0 @ X0 @ sk_C) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((r2_hidden @ (k3_xboole_0 @ sk_B_1 @ sk_C) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '22'])).
% 0.20/0.49  thf(t9_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.49               ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ A ) =>
% 0.20/0.49                 ( ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ (k2_yellow_1 @ X36)))
% 0.20/0.49          | ~ (r2_hidden @ (k3_xboole_0 @ X35 @ X37) @ X36)
% 0.20/0.49          | ((k11_lattice3 @ (k2_yellow_1 @ X36) @ X35 @ X37)
% 0.20/0.49              = (k3_xboole_0 @ X35 @ X37))
% 0.20/0.49          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ (k2_yellow_1 @ X36)))
% 0.20/0.49          | (v1_xboole_0 @ X36))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_yellow_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X35 @ X36)
% 0.20/0.49          | ~ (r2_hidden @ (k3_xboole_0 @ X35 @ X37) @ X36)
% 0.20/0.49          | ((k11_lattice3 @ (k2_yellow_1 @ X36) @ X35 @ X37)
% 0.20/0.49              = (k3_xboole_0 @ X35 @ X37))
% 0.20/0.49          | ~ (m1_subset_1 @ X37 @ X36)
% 0.20/0.49          | (v1_xboole_0 @ X36))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k11_lattice3 @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1 @ sk_C)
% 0.20/0.49            = (k3_xboole_0 @ sk_B_1 @ sk_C))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '27'])).
% 0.20/0.49  thf('29', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k2_yellow_1 @ (k9_setfam_1 @ X31)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf('31', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('32', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(redefinition_k12_lattice3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (l1_orders_2 @ X12)
% 0.20/0.49          | ~ (v2_lattice3 @ X12)
% 0.20/0.49          | ~ (v5_orders_2 @ X12)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.49          | ((k12_lattice3 @ X12 @ X11 @ X13)
% 0.20/0.49              = (k11_lattice3 @ X12 @ X11 @ X13)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ((k12_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k11_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | ~ (v5_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (l1_orders_2 @ (k3_yellow_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(fc7_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v4_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v3_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( ~( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) ))).
% 0.20/0.49  thf('37', plain, (![X25 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.49  thf(d2_yellow_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.49  thf(fc1_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.49         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.49         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.49         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.49         ( v1_lattice3 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.49         ( v2_lattice3 @ ( k3_lattice3 @ A ) ) ) ))).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X20 : $i]:
% 0.20/0.49         ((v2_lattice3 @ (k3_lattice3 @ X20))
% 0.20/0.49          | ~ (l3_lattices @ X20)
% 0.20/0.49          | ~ (v10_lattices @ X20)
% 0.20/0.49          | (v2_struct_0 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_yellow_1])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.20/0.49          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.20/0.49          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf(fc2_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v10_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.49       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.49  thf('41', plain, (![X10 : $i]: (v10_lattices @ (k1_lattice3 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.20/0.49  thf(dt_k1_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.49       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.49  thf('42', plain, (![X6 : $i]: (l3_lattices @ (k1_lattice3 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.49  thf(fc1_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.49       ( ~( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) ))).
% 0.20/0.49  thf('44', plain, (![X7 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.49  thf('45', plain, (![X0 : $i]: (v2_lattice3 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf(dt_k3_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ))).
% 0.20/0.49  thf('46', plain, (![X19 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k3_yellow_1])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ((k12_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k11_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k9_setfam_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '36', '37', '45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)
% 0.20/0.49              = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49         = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '48'])).
% 0.20/0.49  thf('50', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49            = (k3_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29', '30', '49', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          != (k2_xboole_0 @ sk_B_1 @ sk_C))
% 0.20/0.49        | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49            != (k3_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      ((((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          != (k3_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49                = (k3_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['52'])).
% 0.20/0.49  thf('54', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('55', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X26 @ (k9_setfam_1 @ X27))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X28 @ X26) @ (k9_setfam_1 @ X27))
% 0.20/0.49          | ~ (m1_subset_1 @ X28 @ (k9_setfam_1 @ X27)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X0 @ sk_C) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      ((r2_hidden @ (k2_xboole_0 @ sk_B_1 @ sk_C) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['54', '57'])).
% 0.20/0.49  thf(t8_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.49               ( ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ A ) =>
% 0.20/0.49                 ( ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) =
% 0.20/0.49                   ( k2_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ (k2_yellow_1 @ X33)))
% 0.20/0.49          | ~ (r2_hidden @ (k2_xboole_0 @ X32 @ X34) @ X33)
% 0.20/0.49          | ((k10_lattice3 @ (k2_yellow_1 @ X33) @ X32 @ X34)
% 0.20/0.49              = (k2_xboole_0 @ X32 @ X34))
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ (k2_yellow_1 @ X33)))
% 0.20/0.49          | (v1_xboole_0 @ X33))),
% 0.20/0.49      inference('cnf', [status(esa)], [t8_yellow_1])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X32 @ X33)
% 0.20/0.49          | ~ (r2_hidden @ (k2_xboole_0 @ X32 @ X34) @ X33)
% 0.20/0.49          | ((k10_lattice3 @ (k2_yellow_1 @ X33) @ X32 @ X34)
% 0.20/0.49              = (k2_xboole_0 @ X32 @ X34))
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ X33)
% 0.20/0.49          | (v1_xboole_0 @ X33))),
% 0.20/0.49      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k10_lattice3 @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1 @ sk_C)
% 0.20/0.49            = (k2_xboole_0 @ sk_B_1 @ sk_C))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['58', '62'])).
% 0.20/0.49  thf('64', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k2_yellow_1 @ (k9_setfam_1 @ X31)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf('66', plain, ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('67', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(redefinition_k13_lattice3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.49          | ~ (l1_orders_2 @ X15)
% 0.20/0.49          | ~ (v1_lattice3 @ X15)
% 0.20/0.49          | ~ (v5_orders_2 @ X15)
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.49          | ((k13_lattice3 @ X15 @ X14 @ X16)
% 0.20/0.49              = (k10_lattice3 @ X15 @ X14 @ X16)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ((k13_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k10_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | ~ (v5_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | ~ (l1_orders_2 @ (k3_yellow_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('72', plain, (![X25 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (![X20 : $i]:
% 0.20/0.49         ((v1_lattice3 @ (k3_lattice3 @ X20))
% 0.20/0.49          | ~ (l3_lattices @ X20)
% 0.20/0.49          | ~ (v10_lattices @ X20)
% 0.20/0.49          | (v2_struct_0 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_yellow_1])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.20/0.49          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.20/0.49          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['73', '74'])).
% 0.20/0.49  thf('76', plain, (![X10 : $i]: (v10_lattices @ (k1_lattice3 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.20/0.49  thf('77', plain, (![X6 : $i]: (l3_lattices @ (k1_lattice3 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.20/0.49  thf('79', plain, (![X7 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.49  thf('80', plain, (![X0 : $i]: (v1_lattice3 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['78', '79'])).
% 0.20/0.49  thf('81', plain, (![X19 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k3_yellow_1])).
% 0.20/0.49  thf('82', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ((k13_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k10_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k9_setfam_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['70', '71', '72', '80', '81'])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | ((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)
% 0.20/0.49              = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['67', '82'])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49         = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['66', '83'])).
% 0.20/0.49  thf('85', plain, ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49            = (k2_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '64', '65', '84', '85'])).
% 0.20/0.49  thf('87', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49         = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.49  thf('89', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          != (k2_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49                = (k2_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['52'])).
% 0.20/0.49  thf('90', plain,
% 0.20/0.49      ((((k2_xboole_0 @ sk_B_1 @ sk_C) != (k2_xboole_0 @ sk_B_1 @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49                = (k2_xboole_0 @ sk_B_1 @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          = (k2_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.49  thf('92', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          = (k3_xboole_0 @ sk_B_1 @ sk_C))) | 
% 0.20/0.49       ~
% 0.20/0.49       (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          = (k2_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['52'])).
% 0.20/0.49  thf('93', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49          = (k3_xboole_0 @ sk_B_1 @ sk_C)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.49         != (k3_xboole_0 @ sk_B_1 @ sk_C))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['53', '93'])).
% 0.20/0.49  thf('95', plain, ((v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['51', '94'])).
% 0.20/0.49  thf('96', plain, ($false), inference('demod', [status(thm)], ['13', '95'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
