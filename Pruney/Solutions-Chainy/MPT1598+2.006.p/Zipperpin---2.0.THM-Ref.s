%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ajyqv61zx

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:05 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 335 expanded)
%              Number of leaves         :   31 ( 127 expanded)
%              Depth                    :   17
%              Number of atoms          : 1170 (3853 expanded)
%              Number of equality atoms :   20 ( 160 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

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

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k10_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k10_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k10_lattice3 @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_lattice3])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('11',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(l26_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k10_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ B @ D )
                      & ( r1_orders_2 @ A @ C @ D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ B @ E )
                              & ( r1_orders_2 @ A @ C @ E ) )
                           => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( X11
       != ( k10_lattice3 @ X10 @ X9 @ X12 ) )
      | ( r1_orders_2 @ X10 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ X12 @ ( k10_lattice3 @ X10 @ X9 @ X12 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X10 @ X9 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('21',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('22',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('29',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('34',plain,(
    ! [X20: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('35',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('40',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X27 ) @ X26 @ X28 )
      | ( r1_tarski @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('43',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('44',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('45',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X27 ) @ X26 @ X28 )
      | ( r1_tarski @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('49',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X23: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X23 ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('51',plain,
    ( ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('55',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( X11
       != ( k10_lattice3 @ X10 @ X9 @ X12 ) )
      | ( r1_orders_2 @ X10 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('57',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ X9 @ ( k10_lattice3 @ X10 @ X9 @ X12 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X10 @ X9 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('60',plain,(
    ! [X24: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('61',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('62',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('68',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('70',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('73',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X27 ) @ X26 @ X28 )
      | ( r1_tarski @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('79',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X23: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X23 ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('81',plain,
    ( ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['81','82'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['53','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ajyqv61zx
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:28:04 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  % Running portfolio for 600 s
% 0.18/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.18/0.34  % Number of cores: 8
% 0.18/0.34  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 228 iterations in 0.395s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.68/0.88  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.68/0.88  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.68/0.88  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.68/0.88  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.68/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.68/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.68/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.88  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.68/0.88  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.68/0.88  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.68/0.88  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.68/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.88  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.68/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.88  thf(t6_yellow_1, conjecture,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.68/0.88       ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.68/0.88         ( ![B:$i]:
% 0.68/0.88           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.68/0.88             ( ![C:$i]:
% 0.68/0.88               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.68/0.88                 ( r1_tarski @
% 0.68/0.88                   ( k2_xboole_0 @ B @ C ) @ 
% 0.68/0.88                   ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i]:
% 0.68/0.88        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.68/0.88          ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.68/0.88            ( ![B:$i]:
% 0.68/0.88              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.68/0.88                ( ![C:$i]:
% 0.68/0.88                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.68/0.88                    ( r1_tarski @
% 0.68/0.88                      ( k2_xboole_0 @ B @ C ) @ 
% 0.68/0.88                      ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t6_yellow_1])).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      (~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.68/0.88          (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t1_yellow_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.68/0.88       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.68/0.88  thf('2', plain, (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('3', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('5', plain, (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('6', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf('7', plain, (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf(dt_k10_lattice3, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.68/0.88         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88       ( m1_subset_1 @ ( k10_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.68/0.88          | ~ (l1_orders_2 @ X7)
% 0.68/0.88          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.68/0.88          | (m1_subset_1 @ (k10_lattice3 @ X7 @ X6 @ X8) @ (u1_struct_0 @ X7)))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k10_lattice3])).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X1 @ X0)
% 0.68/0.88          | (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.68/0.88             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.68/0.88          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf(dt_k2_yellow_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.68/0.88       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.68/0.88  thf('12', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X1 @ X0)
% 0.68/0.88          | (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.68/0.88          | (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.68/0.88             sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['6', '13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.68/0.88        sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '14'])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf(l26_lattice3, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.68/0.88         ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88           ( ![C:$i]:
% 0.68/0.88             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88               ( ![D:$i]:
% 0.68/0.88                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88                   ( ( ( D ) = ( k10_lattice3 @ A @ B @ C ) ) <=>
% 0.68/0.88                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.68/0.88                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.68/0.88                       ( ![E:$i]:
% 0.68/0.88                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.68/0.88                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.68/0.88                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.68/0.88          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.68/0.88          | ((X11) != (k10_lattice3 @ X10 @ X9 @ X12))
% 0.68/0.88          | (r1_orders_2 @ X10 @ X12 @ X11)
% 0.68/0.88          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.68/0.88          | ~ (l1_orders_2 @ X10)
% 0.68/0.88          | ~ (v1_lattice3 @ X10)
% 0.68/0.88          | ~ (v5_orders_2 @ X10)
% 0.68/0.88          | (v2_struct_0 @ X10))),
% 0.68/0.88      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.68/0.88         ((v2_struct_0 @ X10)
% 0.68/0.88          | ~ (v5_orders_2 @ X10)
% 0.68/0.88          | ~ (v1_lattice3 @ X10)
% 0.68/0.88          | ~ (l1_orders_2 @ X10)
% 0.68/0.88          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.68/0.88          | (r1_orders_2 @ X10 @ X12 @ (k10_lattice3 @ X10 @ X9 @ X12))
% 0.68/0.88          | ~ (m1_subset_1 @ (k10_lattice3 @ X10 @ X9 @ X12) @ 
% 0.68/0.88               (u1_struct_0 @ X10))
% 0.68/0.88          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['17'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.68/0.88          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.68/0.88             (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))
% 0.68/0.88          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.68/0.88          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['16', '18'])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('22', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.68/0.88  thf(fc5_yellow_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.68/0.88       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.68/0.88       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.68/0.88       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.68/0.88  thf('23', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ X0)
% 0.68/0.88          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.68/0.88             (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))
% 0.68/0.88          | ~ (m1_subset_1 @ X1 @ X0)
% 0.68/0.88          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.68/0.88        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['15', '24'])).
% 0.68/0.88  thf('26', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('27', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('28', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf(redefinition_r3_orders_2, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.68/0.88         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.68/0.88         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.68/0.88          | ~ (l1_orders_2 @ X4)
% 0.68/0.88          | ~ (v3_orders_2 @ X4)
% 0.68/0.88          | (v2_struct_0 @ X4)
% 0.68/0.88          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.68/0.88          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.68/0.88          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X1 @ X0)
% 0.68/0.88          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.68/0.88          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.68/0.88          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('34', plain, (![X20 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X20))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.68/0.88  thf('35', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.68/0.88  thf('36', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X1 @ X0)
% 0.68/0.88          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.68/0.88          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ X0)
% 0.68/0.88          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | ~ (m1_subset_1 @ 
% 0.68/0.88             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.68/0.88        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['29', '36'])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.68/0.88        sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '14'])).
% 0.68/0.88  thf('39', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.68/0.88         (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['40'])).
% 0.68/0.88  thf(t3_yellow_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.68/0.88           ( ![C:$i]:
% 0.68/0.88             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.68/0.88               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.68/0.88                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ (k2_yellow_1 @ X27)))
% 0.68/0.88          | ~ (r3_orders_2 @ (k2_yellow_1 @ X27) @ X26 @ X28)
% 0.68/0.88          | (r1_tarski @ X26 @ X28)
% 0.68/0.88          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k2_yellow_1 @ X27)))
% 0.68/0.88          | (v1_xboole_0 @ X27))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X26 @ X27)
% 0.68/0.88          | ~ (r3_orders_2 @ (k2_yellow_1 @ X27) @ X26 @ X28)
% 0.68/0.88          | (r1_tarski @ X26 @ X28)
% 0.68/0.88          | ~ (m1_subset_1 @ X28 @ X27)
% 0.68/0.88          | (v1_xboole_0 @ X27))),
% 0.68/0.88      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (v1_xboole_0 @ sk_A)
% 0.68/0.88        | ~ (m1_subset_1 @ 
% 0.68/0.88             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.68/0.88        | (r1_tarski @ sk_C @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['41', '45'])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.68/0.88        sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '14'])).
% 0.68/0.88  thf('48', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (v1_xboole_0 @ sk_A)
% 0.68/0.88        | (r1_tarski @ sk_C @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.68/0.88  thf(fc6_yellow_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.68/0.88       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.68/0.88         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (![X23 : $i]:
% 0.68/0.88         (~ (v2_struct_0 @ (k2_yellow_1 @ X23)) | (v1_xboole_0 @ X23))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | (v1_xboole_0 @ sk_A))),
% 0.68/0.88      inference('clc', [status(thm)], ['49', '50'])).
% 0.68/0.88  thf('52', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      ((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.68/0.88      inference('clc', [status(thm)], ['51', '52'])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.68/0.88        sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '14'])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.68/0.88          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.68/0.88          | ((X11) != (k10_lattice3 @ X10 @ X9 @ X12))
% 0.68/0.88          | (r1_orders_2 @ X10 @ X9 @ X11)
% 0.68/0.88          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.68/0.88          | ~ (l1_orders_2 @ X10)
% 0.68/0.88          | ~ (v1_lattice3 @ X10)
% 0.68/0.88          | ~ (v5_orders_2 @ X10)
% 0.68/0.88          | (v2_struct_0 @ X10))),
% 0.68/0.88      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.68/0.88         ((v2_struct_0 @ X10)
% 0.68/0.88          | ~ (v5_orders_2 @ X10)
% 0.68/0.88          | ~ (v1_lattice3 @ X10)
% 0.68/0.88          | ~ (l1_orders_2 @ X10)
% 0.68/0.88          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.68/0.88          | (r1_orders_2 @ X10 @ X9 @ (k10_lattice3 @ X10 @ X9 @ X12))
% 0.68/0.88          | ~ (m1_subset_1 @ (k10_lattice3 @ X10 @ X9 @ X12) @ 
% 0.68/0.88               (u1_struct_0 @ X10))
% 0.68/0.88          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['56'])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.68/0.88          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ 
% 0.68/0.88             (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))
% 0.68/0.88          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.68/0.88          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['55', '57'])).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (![X24 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X24)) = (X24))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.68/0.88  thf('61', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.68/0.88  thf('62', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ X0)
% 0.68/0.88          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ 
% 0.68/0.88             (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))
% 0.68/0.88          | ~ (m1_subset_1 @ X1 @ X0)
% 0.68/0.88          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.68/0.88          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.68/0.88        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['54', '63'])).
% 0.68/0.88  thf('65', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('66', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('67', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf('68', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X1 @ X0)
% 0.68/0.88          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.68/0.88          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ X0)
% 0.68/0.88          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | ~ (m1_subset_1 @ 
% 0.68/0.88             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.68/0.88        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['68', '69'])).
% 0.68/0.88  thf('71', plain,
% 0.68/0.88      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.68/0.88        sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '14'])).
% 0.68/0.88  thf('72', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf('73', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.68/0.88  thf('74', plain,
% 0.68/0.88      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.68/0.88         (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['73'])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X26 @ X27)
% 0.68/0.88          | ~ (r3_orders_2 @ (k2_yellow_1 @ X27) @ X26 @ X28)
% 0.68/0.88          | (r1_tarski @ X26 @ X28)
% 0.68/0.88          | ~ (m1_subset_1 @ X28 @ X27)
% 0.68/0.88          | (v1_xboole_0 @ X27))),
% 0.68/0.88      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.68/0.88  thf('76', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (v1_xboole_0 @ sk_A)
% 0.68/0.88        | ~ (m1_subset_1 @ 
% 0.68/0.88             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.68/0.88        | (r1_tarski @ sk_B @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['74', '75'])).
% 0.68/0.88  thf('77', plain,
% 0.68/0.88      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.68/0.88        sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '14'])).
% 0.68/0.88  thf('78', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.68/0.88        | (v1_xboole_0 @ sk_A)
% 0.68/0.88        | (r1_tarski @ sk_B @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.68/0.88  thf('80', plain,
% 0.68/0.88      (![X23 : $i]:
% 0.68/0.88         (~ (v2_struct_0 @ (k2_yellow_1 @ X23)) | (v1_xboole_0 @ X23))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.68/0.88  thf('81', plain,
% 0.68/0.88      (((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88        | (v1_xboole_0 @ sk_A))),
% 0.68/0.88      inference('clc', [status(thm)], ['79', '80'])).
% 0.68/0.88  thf('82', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('83', plain,
% 0.68/0.88      ((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.68/0.88      inference('clc', [status(thm)], ['81', '82'])).
% 0.68/0.88  thf(t8_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.68/0.88       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.68/0.88  thf('84', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r1_tarski @ X0 @ X1)
% 0.68/0.88          | ~ (r1_tarski @ X2 @ X1)
% 0.68/0.88          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.68/0.88  thf('85', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 0.68/0.88           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.68/0.88          | ~ (r1_tarski @ X0 @ 
% 0.68/0.88               (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['83', '84'])).
% 0.68/0.88  thf('86', plain,
% 0.68/0.88      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.68/0.88        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.68/0.88      inference('sup-', [status(thm)], ['53', '85'])).
% 0.68/0.88  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.75/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
