%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1960+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vzoOml4XYd

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 269 expanded)
%              Number of leaves         :   55 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          : 1388 (2231 expanded)
%              Number of equality atoms :   83 ( 135 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v2_waybel_1_type,type,(
    v2_waybel_1: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(v10_waybel_1_type,type,(
    v10_waybel_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v11_waybel_1_type,type,(
    v11_waybel_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(r6_waybel_1_type,type,(
    r6_waybel_1: $i > $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v3_yellow_0_type,type,(
    v3_yellow_0: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_waybel_1_type,type,(
    k7_waybel_1: $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t9_waybel_7,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ( ( k7_waybel_1 @ ( k3_yellow_1 @ A ) @ B )
        = ( k6_subset_1 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
       => ( ( k7_waybel_1 @ ( k3_yellow_1 @ A ) @ B )
          = ( k6_subset_1 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_waybel_7])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X26: $i] :
      ( ( k9_setfam_1 @ X26 )
      = ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k9_setfam_1 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41
        = ( k2_xboole_0 @ X40 @ ( k4_xboole_0 @ X41 @ X40 ) ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41
        = ( k2_xboole_0 @ X40 @ ( k6_subset_1 @ X41 @ X40 ) ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('12',plain,(
    ! [X26: $i] :
      ( ( k9_setfam_1 @ X26 )
      = ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k9_setfam_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('15',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v1_lattice3 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( ( k13_lattice3 @ X22 @ X21 @ X23 )
        = ( k10_lattice3 @ X22 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(fc7_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ~ ( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X17: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf(dt_k3_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf(cc8_waybel_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v11_waybel_1 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_yellow_0 @ A )
          & ( v2_waybel_1 @ A )
          & ( v10_waybel_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v11_waybel_1 @ X0 )
      | ( v1_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc8_waybel_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_waybel_7,axiom,(
    ! [A: $i] :
      ( ( v11_waybel_1 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X12: $i] :
      ( v11_waybel_1 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_waybel_7])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k9_setfam_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t17_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
         => ( ( ( k13_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
              = ( k2_xboole_0 @ B @ C ) )
            & ( ( k12_lattice3 @ ( k3_yellow_1 @ A ) @ B @ C )
              = ( k3_xboole_0 @ B @ C ) ) ) ) ) )).

thf('33',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X33 ) @ X34 @ X32 )
        = ( k2_xboole_0 @ X34 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_1])).

thf('34',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('35',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('36',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k9_setfam_1 @ X33 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X33 ) @ X34 @ X32 )
        = ( k2_xboole_0 @ X34 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k9_setfam_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k13_lattice3 @ ( k3_yellow_1 @ X0 ) @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k2_xboole_0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k13_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('41',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(d23_waybel_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r6_waybel_1 @ A @ B @ C )
              <=> ( ( ( k10_lattice3 @ A @ B @ C )
                    = ( k4_yellow_0 @ A ) )
                  & ( ( k11_lattice3 @ A @ B @ C )
                    = ( k3_yellow_0 @ A ) ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ( ( k10_lattice3 @ X2 @ X1 @ X3 )
       != ( k4_yellow_0 @ X2 ) )
      | ( ( k11_lattice3 @ X2 @ X1 @ X3 )
       != ( k3_yellow_0 @ X2 ) )
      | ( r6_waybel_1 @ X2 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d23_waybel_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( r6_waybel_1 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
       != ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
       != ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('45',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(t18_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X35: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X35 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t18_yellow_1])).

thf(t19_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf('47',plain,(
    ! [X36: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t19_yellow_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) )
      | ( r6_waybel_1 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
       != k1_xboole_0 )
      | ( ( k10_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k10_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
       != sk_A )
      | ( ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r6_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != sk_A )
      | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k9_setfam_1 @ sk_A ) )
      | ( r6_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      | ( ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k9_setfam_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k9_setfam_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('54',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( ( k12_lattice3 @ X19 @ X18 @ X20 )
        = ( k11_lattice3 @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('58',plain,(
    ! [X17: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('59',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v11_waybel_1 @ X0 )
      | ( v2_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc8_waybel_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i] :
      ( v11_waybel_1 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_waybel_7])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X13: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('71',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k9_setfam_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('72',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X33 ) @ X34 @ X32 )
        = ( k3_xboole_0 @ X34 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_1])).

thf('73',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('74',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('75',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k9_setfam_1 @ X33 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X33 ) @ X34 @ X32 )
        = ( k3_xboole_0 @ X34 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k9_setfam_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k12_lattice3 @ ( k3_yellow_1 @ X0 ) @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k12_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k11_lattice3 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != sk_A )
      | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) )
      | ( r6_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      | ( ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51','78'])).

thf('80',plain,
    ( ( sk_A != sk_A )
    | ( ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) )
     != k1_xboole_0 )
    | ( r6_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','79'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('81',plain,(
    ! [X43: $i,X44: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X43 @ X44 ) @ X44 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('82',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('83',plain,(
    ! [X43: $i,X44: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X43 @ X44 ) @ X44 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('84',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('86',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A != sk_A )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( r6_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) )
    | ( r6_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X13: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('91',plain,(
    r6_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('93',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(t11_yellow_5,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v11_waybel_1 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r6_waybel_1 @ A @ B @ C )
              <=> ( C
                  = ( k7_waybel_1 @ A @ B ) ) ) ) ) ) )).

thf('94',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r6_waybel_1 @ X30 @ X29 @ X31 )
      | ( X31
        = ( k7_waybel_1 @ X30 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_orders_2 @ X30 )
      | ~ ( v11_waybel_1 @ X30 )
      | ~ ( v2_lattice3 @ X30 )
      | ~ ( v1_lattice3 @ X30 )
      | ~ ( v5_orders_2 @ X30 )
      | ~ ( v4_orders_2 @ X30 )
      | ~ ( v3_orders_2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t11_yellow_5])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ( X2
        = ( k7_waybel_1 @ ( k3_yellow_1 @ X0 ) @ X1 ) )
      | ~ ( r6_waybel_1 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X15: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('97',plain,(
    ! [X16: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('98',plain,(
    ! [X17: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('100',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('101',plain,(
    ! [X12: $i] :
      ( v11_waybel_1 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_waybel_7])).

thf('102',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('103',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) )
      = ( k9_setfam_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X0 ) )
      | ( X2
        = ( k7_waybel_1 @ ( k3_yellow_1 @ X0 ) @ X1 ) )
      | ~ ( r6_waybel_1 @ ( k3_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100','101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r6_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B @ X0 )
      | ( X0
        = ( k7_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','104'])).

thf('106',plain,
    ( ~ ( m1_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k6_subset_1 @ sk_A @ sk_B )
      = ( k7_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','105'])).

thf('107',plain,(
    ! [X9: $i,X10: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X9 @ X10 ) @ ( k9_setfam_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('108',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k7_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ( k7_waybel_1 @ ( k3_yellow_1 @ sk_A ) @ sk_B )
 != ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).


%------------------------------------------------------------------------------
