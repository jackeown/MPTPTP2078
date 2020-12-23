%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Aia20VNaUg

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 203 expanded)
%              Number of leaves         :   44 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          : 1199 (2500 expanded)
%              Number of equality atoms :   57 ( 145 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l19_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
         => ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) )
            & ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X25 @ X23 ) @ ( k9_setfam_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[l19_yellow_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X0 @ sk_B ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_B @ sk_B ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) )
      | ( r2_hidden @ ( k3_xboole_0 @ X25 @ X23 ) @ ( k9_setfam_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[l19_yellow_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

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

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) ) )
      | ~ ( r2_hidden @ ( k3_xboole_0 @ X30 @ X32 ) @ X31 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X31 ) @ X30 @ X32 )
        = ( k3_xboole_0 @ X30 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) ) )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) @ X1 @ X2 )
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('17',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
    | ( ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v2_lattice3 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k12_lattice3 @ X9 @ X8 @ X10 )
        = ( k11_lattice3 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X17: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','28','31'])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('33',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
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

thf('34',plain,(
    ! [X18: $i] :
      ( ( v2_lattice3 @ ( k3_lattice3 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(fc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( v10_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('36',plain,(
    ! [X7: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf(dt_k1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(fc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( v3_lattices @ ( k1_lattice3 @ A ) )
      & ~ ( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) )).

thf('39',plain,(
    ! [X4: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('40',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,
    ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21','42'])).

thf('44',plain,
    ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X25 @ X23 ) @ ( k9_setfam_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[l19_yellow_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k2_xboole_0 @ X0 @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k9_setfam_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

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

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ~ ( r2_hidden @ ( k2_xboole_0 @ X27 @ X29 ) @ X28 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
        = ( k2_xboole_0 @ X27 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_yellow_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) @ X1 @ X2 )
        = ( k2_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('56',plain,(
    ! [X26: $i] :
      ( ( k3_yellow_1 @ X26 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k2_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
    | ( ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v1_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( ( k13_lattice3 @ X12 @ X11 @ X13 )
        = ( k10_lattice3 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
      | ~ ( v1_lattice3 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('70',plain,(
    ! [X18: $i] :
      ( ( v1_lattice3 @ ( k3_lattice3 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X7: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf('73',plain,(
    ! [X3: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X4: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('76',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['68','76'])).

thf('78',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['61','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('81',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['44'])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_C )
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['44'])).

thf('86',plain,(
    ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
 != ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ sk_C )
 != ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['45','86'])).

thf('88',plain,(
    v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['43','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['6','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Aia20VNaUg
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 11:06:53 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 107 iterations in 0.045s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.20/0.49  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.49  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.49  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.49  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.49  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.49  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
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
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l19_yellow_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) =>
% 0.20/0.49           ( ( r2_hidden @ ( k3_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) & 
% 0.20/0.49             ( r2_hidden @ ( k2_xboole_0 @ B @ C ) @ ( k9_setfam_1 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k3_yellow_1 @ X24)))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X25 @ X23) @ (k9_setfam_1 @ X24))
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k3_yellow_1 @ X24))))),
% 0.20/0.49      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X0 @ sk_B) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((r2_hidden @ (k2_xboole_0 @ sk_B @ sk_B) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf(t7_boole, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_boole])).
% 0.20/0.49  thf('6', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k3_yellow_1 @ X24)))
% 0.20/0.49          | (r2_hidden @ (k3_xboole_0 @ X25 @ X23) @ (k9_setfam_1 @ X24))
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k3_yellow_1 @ X24))))),
% 0.20/0.49      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | (r2_hidden @ (k3_xboole_0 @ X0 @ sk_C) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t4_yellow_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
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
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ (k2_yellow_1 @ X31)))
% 0.20/0.49          | ~ (r2_hidden @ (k3_xboole_0 @ X30 @ X32) @ X31)
% 0.20/0.49          | ((k11_lattice3 @ (k2_yellow_1 @ X31) @ X30 @ X32)
% 0.20/0.49              = (k3_xboole_0 @ X30 @ X32))
% 0.20/0.49          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ (k2_yellow_1 @ X31)))
% 0.20/0.49          | (v1_xboole_0 @ X31))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_yellow_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ 
% 0.20/0.49               (u1_struct_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))))
% 0.20/0.49          | ((k11_lattice3 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)) @ X1 @ X2)
% 0.20/0.49              = (k3_xboole_0 @ X1 @ X2))
% 0.20/0.49          | ~ (r2_hidden @ (k3_xboole_0 @ X1 @ X2) @ (k9_setfam_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | ((k11_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k3_xboole_0 @ X1 @ X2))
% 0.20/0.49          | ~ (r2_hidden @ (k3_xboole_0 @ X1 @ X2) @ (k9_setfam_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k3_xboole_0 @ sk_B @ X0) @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | ((k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49              = (k3_xboole_0 @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | (v1_xboole_0 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49        | ((k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49            = (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k12_lattice3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.49          | ~ (l1_orders_2 @ X9)
% 0.20/0.49          | ~ (v2_lattice3 @ X9)
% 0.20/0.49          | ~ (v5_orders_2 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.49          | ((k12_lattice3 @ X9 @ X8 @ X10) = (k11_lattice3 @ X9 @ X8 @ X10)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49            = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | ~ (v5_orders_2 @ (k3_yellow_1 @ sk_A))
% 0.20/0.49          | ~ (v2_lattice3 @ (k3_yellow_1 @ sk_A))
% 0.20/0.49          | ~ (l1_orders_2 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf(fc5_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.49  thf('27', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.49  thf('28', plain, (![X0 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf(dt_k2_yellow_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.49       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.49  thf('30', plain, (![X17 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.49  thf('31', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49            = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | ~ (v2_lattice3 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '28', '31'])).
% 0.20/0.49  thf(d2_yellow_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
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
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X18 : $i]:
% 0.20/0.49         ((v2_lattice3 @ (k3_lattice3 @ X18))
% 0.20/0.49          | ~ (l3_lattices @ X18)
% 0.20/0.49          | ~ (v10_lattices @ X18)
% 0.20/0.49          | (v2_struct_0 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_yellow_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.20/0.49          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.20/0.49          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf(fc2_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v10_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.49       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.49  thf('36', plain, (![X7 : $i]: (v10_lattices @ (k1_lattice3 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.20/0.49  thf(dt_k1_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.49       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.49  thf('37', plain, (![X3 : $i]: (l3_lattices @ (k1_lattice3 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.49  thf(fc1_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.49       ( ~( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) ))).
% 0.20/0.49  thf('39', plain, (![X4 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.49  thf('40', plain, (![X0 : $i]: (v2_lattice3 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49            = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49         = (k11_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49            = (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49          != (k2_xboole_0 @ sk_B @ sk_C))
% 0.20/0.49        | ((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49            != (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49          != (k3_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49                = (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k3_yellow_1 @ X24)))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X25 @ X23) @ (k9_setfam_1 @ X24))
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k3_yellow_1 @ X24))))),
% 0.20/0.49      inference('cnf', [status(esa)], [l19_yellow_1])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | (r2_hidden @ (k2_xboole_0 @ X0 @ sk_C) @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((r2_hidden @ (k2_xboole_0 @ sk_B @ sk_C) @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
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
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.20/0.49          | ~ (r2_hidden @ (k2_xboole_0 @ X27 @ X29) @ X28)
% 0.20/0.49          | ((k10_lattice3 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.20/0.49              = (k2_xboole_0 @ X27 @ X29))
% 0.20/0.49          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.20/0.49          | (v1_xboole_0 @ X28))),
% 0.20/0.49      inference('cnf', [status(esa)], [t8_yellow_1])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ 
% 0.20/0.49               (u1_struct_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))))
% 0.20/0.49          | ((k10_lattice3 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)) @ X1 @ X2)
% 0.20/0.49              = (k2_xboole_0 @ X1 @ X2))
% 0.20/0.49          | ~ (r2_hidden @ (k2_xboole_0 @ X1 @ X2) @ (k9_setfam_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X26 : $i]: ((k3_yellow_1 @ X26) = (k2_yellow_1 @ (k9_setfam_1 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.49          | ((k10_lattice3 @ (k3_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.49              = (k2_xboole_0 @ X1 @ X2))
% 0.20/0.49          | ~ (r2_hidden @ (k2_xboole_0 @ X1 @ X2) @ (k9_setfam_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k2_xboole_0 @ sk_B @ X0) @ (k9_setfam_1 @ sk_A))
% 0.20/0.49          | ((k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49              = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | (v1_xboole_0 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['51', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49        | ((k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49            = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k13_lattice3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (l1_orders_2 @ X12)
% 0.20/0.49          | ~ (v1_lattice3 @ X12)
% 0.20/0.49          | ~ (v5_orders_2 @ X12)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.49          | ((k13_lattice3 @ X12 @ X11 @ X13)
% 0.20/0.49              = (k10_lattice3 @ X12 @ X11 @ X13)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49            = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | ~ (v5_orders_2 @ (k3_yellow_1 @ sk_A))
% 0.20/0.49          | ~ (v1_lattice3 @ (k3_yellow_1 @ sk_A))
% 0.20/0.49          | ~ (l1_orders_2 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('65', plain, (![X0 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49            = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | ~ (v5_orders_2 @ (k3_yellow_1 @ sk_A))
% 0.20/0.49          | ~ (v1_lattice3 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.49  thf('67', plain, (![X0 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49            = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))
% 0.20/0.49          | ~ (v1_lattice3 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X18 : $i]:
% 0.20/0.49         ((v1_lattice3 @ (k3_lattice3 @ X18))
% 0.20/0.49          | ~ (l3_lattices @ X18)
% 0.20/0.49          | ~ (v10_lattices @ X18)
% 0.20/0.49          | (v2_struct_0 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_yellow_1])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.20/0.49          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.20/0.49          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain, (![X7 : $i]: (v10_lattices @ (k1_lattice3 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.20/0.49  thf('73', plain, (![X3 : $i]: (l3_lattices @ (k1_lattice3 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_lattice3 @ (k3_yellow_1 @ X0))
% 0.20/0.49          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.20/0.49  thf('75', plain, (![X4 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.49  thf('76', plain, (![X0 : $i]: (v1_lattice3 @ (k3_yellow_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.49            = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['68', '76'])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49         = (k10_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['61', '77'])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.20/0.49        | ((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49            = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['59', '60', '78'])).
% 0.20/0.49  thf('80', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('81', plain,
% 0.20/0.49      (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['79', '80'])).
% 0.20/0.49  thf('82', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49          != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49                = (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      ((((k2_xboole_0 @ sk_B @ sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49                = (k2_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      ((((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49          = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.49  thf('85', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49          = (k3_xboole_0 @ sk_B @ sk_C))) | 
% 0.20/0.49       ~
% 0.20/0.49       (((k13_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49          = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49          = (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.20/0.49  thf('87', plain,
% 0.20/0.49      (((k12_lattice3 @ (k3_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.49         != (k3_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['45', '86'])).
% 0.20/0.49  thf('88', plain, ((v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['43', '87'])).
% 0.20/0.49  thf('89', plain, ($false), inference('demod', [status(thm)], ['6', '88'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
