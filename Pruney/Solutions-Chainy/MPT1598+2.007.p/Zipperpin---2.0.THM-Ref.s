%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tQXUu1PVLt

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:05 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 272 expanded)
%              Number of leaves         :   30 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          : 1166 (3902 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t6_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
               => ( r1_tarski @ ( k2_xboole_0 @ B @ C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) )
         => ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
                 => ( r1_tarski @ ( k2_xboole_0 @ B @ C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_yellow_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k13_lattice3 @ X10 @ X9 @ X11 )
        = ( k10_lattice3 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('6',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t22_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k13_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ B @ D )
                      & ( r1_orders_2 @ A @ C @ D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ B @ E )
                              & ( r1_orders_2 @ A @ C @ E ) )
                           => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( X14
       != ( k13_lattice3 @ X13 @ X12 @ X15 ) )
      | ( r1_orders_2 @ X13 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t22_yellow_0])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( v5_orders_2 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X15 @ ( k13_lattice3 @ X13 @ X12 @ X15 ) )
      | ~ ( m1_subset_1 @ ( k13_lattice3 @ X13 @ X12 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k10_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k10_lattice3 @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_lattice3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('24',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('26',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['12','19','20','21','22','23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('31',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('35',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X25 ) @ X24 @ X26 )
      | ( r1_tarski @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( X14
       != ( k13_lattice3 @ X13 @ X12 @ X15 ) )
      | ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t22_yellow_0])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( v5_orders_2 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ ( k13_lattice3 @ X13 @ X12 @ X15 ) )
      | ~ ( m1_subset_1 @ ( k13_lattice3 @ X13 @ X12 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('53',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('55',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X20: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('60',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('64',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X25 ) @ X24 @ X26 )
      | ( r1_tarski @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('79',plain,(
    ! [X23: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X23 ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('80',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tQXUu1PVLt
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 281 iterations in 0.373s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.60/0.83  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.60/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.83  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.60/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.60/0.83  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.60/0.83  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.60/0.83  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.60/0.83  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.60/0.83  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.60/0.83  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.60/0.83  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.60/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.83  thf(t6_yellow_1, conjecture,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.83       ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.60/0.83         ( ![B:$i]:
% 0.60/0.83           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.60/0.83             ( ![C:$i]:
% 0.60/0.83               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.60/0.83                 ( r1_tarski @
% 0.60/0.83                   ( k2_xboole_0 @ B @ C ) @ 
% 0.60/0.83                   ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i]:
% 0.60/0.83        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.83          ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.60/0.83            ( ![B:$i]:
% 0.60/0.83              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.60/0.83                ( ![C:$i]:
% 0.60/0.83                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.60/0.83                    ( r1_tarski @
% 0.60/0.83                      ( k2_xboole_0 @ B @ C ) @ 
% 0.60/0.83                      ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t6_yellow_1])).
% 0.60/0.83  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('1', plain,
% 0.60/0.83      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('2', plain,
% 0.60/0.83      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(redefinition_k13_lattice3, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.60/0.83         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.60/0.83         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.83       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.60/0.83  thf('3', plain,
% 0.60/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.83         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.60/0.83          | ~ (l1_orders_2 @ X10)
% 0.60/0.83          | ~ (v1_lattice3 @ X10)
% 0.60/0.83          | ~ (v5_orders_2 @ X10)
% 0.60/0.83          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.60/0.83          | ((k13_lattice3 @ X10 @ X9 @ X11) = (k10_lattice3 @ X10 @ X9 @ X11)))),
% 0.60/0.83      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.60/0.83  thf('4', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.60/0.83            = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.60/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.83          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.60/0.83          | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.60/0.83          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.83  thf(fc5_yellow_1, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.60/0.83       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.60/0.83       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.60/0.83       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.60/0.83  thf('5', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 0.60/0.83      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.60/0.83  thf('6', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(dt_k2_yellow_1, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.60/0.83       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.60/0.83  thf('7', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.60/0.83  thf('8', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.60/0.83            = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.60/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.60/0.83      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.60/0.83  thf('9', plain,
% 0.60/0.83      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.60/0.83         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.60/0.83      inference('sup-', [status(thm)], ['1', '8'])).
% 0.60/0.83  thf(t22_yellow_0, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.83           ( ![C:$i]:
% 0.60/0.83             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.83               ( ![D:$i]:
% 0.60/0.83                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.83                   ( ( ( D ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.60/0.83                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.60/0.83                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.60/0.83                       ( ![E:$i]:
% 0.60/0.83                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.83                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.60/0.83                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.60/0.83                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.83  thf('10', plain,
% 0.60/0.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.60/0.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.60/0.83          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.60/0.83          | ((X14) != (k13_lattice3 @ X13 @ X12 @ X15))
% 0.60/0.83          | (r1_orders_2 @ X13 @ X15 @ X14)
% 0.60/0.83          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.60/0.83          | ~ (l1_orders_2 @ X13)
% 0.60/0.83          | ~ (v1_lattice3 @ X13)
% 0.60/0.83          | ~ (v5_orders_2 @ X13))),
% 0.60/0.83      inference('cnf', [status(esa)], [t22_yellow_0])).
% 0.60/0.83  thf('11', plain,
% 0.60/0.83      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.60/0.83         (~ (v5_orders_2 @ X13)
% 0.60/0.83          | ~ (v1_lattice3 @ X13)
% 0.60/0.83          | ~ (l1_orders_2 @ X13)
% 0.60/0.83          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.60/0.83          | (r1_orders_2 @ X13 @ X15 @ (k13_lattice3 @ X13 @ X12 @ X15))
% 0.60/0.83          | ~ (m1_subset_1 @ (k13_lattice3 @ X13 @ X12 @ X15) @ 
% 0.60/0.83               (u1_struct_0 @ X13))
% 0.60/0.83          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['10'])).
% 0.60/0.83  thf('12', plain,
% 0.60/0.83      ((~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.83           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.83        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.83        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.60/0.83           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.83        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['9', '11'])).
% 0.60/0.84  thf('13', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('14', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(dt_k10_lattice3, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.60/0.84         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.84       ( m1_subset_1 @ ( k10_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.60/0.84  thf('15', plain,
% 0.60/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.60/0.84          | ~ (l1_orders_2 @ X7)
% 0.60/0.84          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.60/0.84          | (m1_subset_1 @ (k10_lattice3 @ X7 @ X6 @ X8) @ (u1_struct_0 @ X7)))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k10_lattice3])).
% 0.60/0.84  thf('16', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.60/0.84           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.84  thf('17', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.60/0.84  thf('18', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.60/0.84           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.60/0.84      inference('demod', [status(thm)], ['16', '17'])).
% 0.60/0.84  thf('19', plain,
% 0.60/0.84      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['13', '18'])).
% 0.60/0.84  thf('20', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.60/0.84         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['1', '8'])).
% 0.60/0.84  thf('22', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('23', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.60/0.84  thf('24', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('25', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.60/0.84        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.60/0.84      inference('demod', [status(thm)],
% 0.60/0.84                ['12', '19', '20', '21', '22', '23', '24', '25'])).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_r3_orders_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.60/0.84         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.60/0.84         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.84       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.60/0.84  thf('28', plain,
% 0.60/0.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.60/0.84          | ~ (l1_orders_2 @ X4)
% 0.60/0.84          | ~ (v3_orders_2 @ X4)
% 0.60/0.84          | (v2_struct_0 @ X4)
% 0.60/0.84          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.60/0.84          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.60/0.84          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.60/0.84  thf('29', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 0.60/0.84          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84          | ~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.60/0.84  thf('30', plain, (![X20 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.60/0.84  thf('31', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 0.60/0.84          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | ~ (m1_subset_1 @ 
% 0.60/0.84             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84             (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['26', '32'])).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['13', '18'])).
% 0.60/0.84  thf('35', plain,
% 0.60/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('demod', [status(thm)], ['33', '34'])).
% 0.60/0.84  thf('36', plain,
% 0.60/0.84      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['13', '18'])).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t3_yellow_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.60/0.84           ( ![C:$i]:
% 0.60/0.84             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.60/0.84               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.60/0.84                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.60/0.84  thf('38', plain,
% 0.60/0.84      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k2_yellow_1 @ X25)))
% 0.60/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ X25) @ X24 @ X26)
% 0.60/0.84          | (r1_tarski @ X24 @ X26)
% 0.60/0.84          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ (k2_yellow_1 @ X25)))
% 0.60/0.84          | (v1_xboole_0 @ X25))),
% 0.60/0.84      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_A)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | (r1_tarski @ sk_C @ X0)
% 0.60/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['37', '38'])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      ((~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | (r1_tarski @ sk_C @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | (v1_xboole_0 @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['36', '39'])).
% 0.60/0.84  thf('41', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('42', plain,
% 0.60/0.84      (((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.60/0.84             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('clc', [status(thm)], ['40', '41'])).
% 0.60/0.84  thf('43', plain,
% 0.60/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | (r1_tarski @ sk_C @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['35', '42'])).
% 0.60/0.84  thf('44', plain,
% 0.60/0.84      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.60/0.84         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['1', '8'])).
% 0.60/0.84  thf('45', plain,
% 0.60/0.84      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.60/0.84          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.60/0.84          | ((X14) != (k13_lattice3 @ X13 @ X12 @ X15))
% 0.60/0.84          | (r1_orders_2 @ X13 @ X12 @ X14)
% 0.60/0.84          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.60/0.84          | ~ (l1_orders_2 @ X13)
% 0.60/0.84          | ~ (v1_lattice3 @ X13)
% 0.60/0.84          | ~ (v5_orders_2 @ X13))),
% 0.60/0.84      inference('cnf', [status(esa)], [t22_yellow_0])).
% 0.60/0.84  thf('46', plain,
% 0.60/0.84      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.60/0.84         (~ (v5_orders_2 @ X13)
% 0.60/0.84          | ~ (v1_lattice3 @ X13)
% 0.60/0.84          | ~ (l1_orders_2 @ X13)
% 0.60/0.84          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.60/0.84          | (r1_orders_2 @ X13 @ X12 @ (k13_lattice3 @ X13 @ X12 @ X15))
% 0.60/0.84          | ~ (m1_subset_1 @ (k13_lattice3 @ X13 @ X12 @ X15) @ 
% 0.60/0.84               (u1_struct_0 @ X13))
% 0.60/0.84          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['45'])).
% 0.60/0.84  thf('47', plain,
% 0.60/0.84      ((~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.60/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['44', '46'])).
% 0.60/0.84  thf('48', plain,
% 0.60/0.84      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['13', '18'])).
% 0.60/0.84  thf('49', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('50', plain,
% 0.60/0.84      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.60/0.84         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['1', '8'])).
% 0.60/0.84  thf('51', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('52', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.60/0.84  thf('53', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('54', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.60/0.84  thf('55', plain,
% 0.60/0.84      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.60/0.84        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.60/0.84      inference('demod', [status(thm)],
% 0.60/0.84                ['47', '48', '49', '50', '51', '52', '53', '54'])).
% 0.60/0.84  thf('56', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('57', plain,
% 0.60/0.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.60/0.84          | ~ (l1_orders_2 @ X4)
% 0.60/0.84          | ~ (v3_orders_2 @ X4)
% 0.60/0.84          | (v2_struct_0 @ X4)
% 0.60/0.84          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.60/0.84          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.60/0.84          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.60/0.84  thf('58', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.60/0.84          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84          | ~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['56', '57'])).
% 0.60/0.84  thf('59', plain, (![X20 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.60/0.84  thf('60', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.60/0.84  thf('61', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.60/0.84          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.60/0.84  thf('62', plain,
% 0.60/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | ~ (m1_subset_1 @ 
% 0.60/0.84             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84             (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['55', '61'])).
% 0.60/0.84  thf('63', plain,
% 0.60/0.84      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['13', '18'])).
% 0.60/0.84  thf('64', plain,
% 0.60/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('demod', [status(thm)], ['62', '63'])).
% 0.60/0.84  thf('65', plain,
% 0.60/0.84      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.60/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['13', '18'])).
% 0.60/0.84  thf('66', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('67', plain,
% 0.60/0.84      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k2_yellow_1 @ X25)))
% 0.60/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ X25) @ X24 @ X26)
% 0.60/0.84          | (r1_tarski @ X24 @ X26)
% 0.60/0.84          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ (k2_yellow_1 @ X25)))
% 0.60/0.84          | (v1_xboole_0 @ X25))),
% 0.60/0.84      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.60/0.84  thf('68', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_A)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.60/0.84          | (r1_tarski @ sk_B @ X0)
% 0.60/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['66', '67'])).
% 0.60/0.84  thf('69', plain,
% 0.60/0.84      ((~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | (r1_tarski @ sk_B @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | (v1_xboole_0 @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['65', '68'])).
% 0.60/0.84  thf('70', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('71', plain,
% 0.60/0.84      (((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.60/0.84             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('clc', [status(thm)], ['69', '70'])).
% 0.60/0.84  thf('72', plain,
% 0.60/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | (r1_tarski @ sk_B @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['64', '71'])).
% 0.60/0.84  thf(t8_xboole_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.60/0.84       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.60/0.84  thf('73', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.60/0.84          | ~ (r1_tarski @ X2 @ X1)
% 0.60/0.84          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.60/0.84      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.60/0.84  thf('74', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 0.60/0.84             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84          | ~ (r1_tarski @ X0 @ 
% 0.60/0.84               (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['72', '73'])).
% 0.60/0.84  thf('75', plain,
% 0.60/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.60/0.84        | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.60/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['43', '74'])).
% 0.60/0.84  thf('76', plain,
% 0.60/0.84      (((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.60/0.84         (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.60/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['75'])).
% 0.60/0.84  thf('77', plain,
% 0.60/0.84      (~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.60/0.84          (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('78', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.60/0.84      inference('clc', [status(thm)], ['76', '77'])).
% 0.60/0.84  thf(fc6_yellow_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.84       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.60/0.84         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.60/0.84  thf('79', plain,
% 0.60/0.84      (![X23 : $i]:
% 0.60/0.84         (~ (v2_struct_0 @ (k2_yellow_1 @ X23)) | (v1_xboole_0 @ X23))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.60/0.84  thf('80', plain, ((v1_xboole_0 @ sk_A)),
% 0.60/0.84      inference('sup-', [status(thm)], ['78', '79'])).
% 0.60/0.84  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
