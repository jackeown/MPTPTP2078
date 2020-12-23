%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bonus0Gb6I

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:04 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 340 expanded)
%              Number of leaves         :   31 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          : 1191 (3920 expanded)
%              Number of equality atoms :   20 ( 160 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

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
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k10_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k10_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k10_lattice3 @ X8 @ X7 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('10',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
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

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( X12
       != ( k10_lattice3 @ X11 @ X10 @ X13 ) )
      | ( r1_orders_2 @ X11 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ X13 @ ( k10_lattice3 @ X11 @ X10 @ X13 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X11 @ X10 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('20',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('21',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X20: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('28',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
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

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('33',plain,(
    ! [X18: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('34',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('39',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X24 ) @ X23 @ X25 )
      | ( r1_tarski @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k2_yellow_1 @ X24 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('42',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('43',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X24 ) @ X23 @ X25 )
      | ( r1_tarski @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('48',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('52',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( X12
       != ( k10_lattice3 @ X11 @ X10 @ X13 ) )
      | ( r1_orders_2 @ X11 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ X10 @ ( k10_lattice3 @ X11 @ X10 @ X13 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X11 @ X10 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('57',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('58',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('59',plain,(
    ! [X20: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('67',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('70',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X24 ) @ X23 @ X25 )
      | ( r1_tarski @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('73',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','80'])).

thf('82',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('86',plain,(
    ! [X6: $i] :
      ( ~ ( v1_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bonus0Gb6I
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:55:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.48/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.73  % Solved by: fo/fo7.sh
% 0.48/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.73  % done 227 iterations in 0.279s
% 0.48/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.73  % SZS output start Refutation
% 0.48/0.73  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.48/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.73  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.48/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.73  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.48/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.73  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.48/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.73  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.48/0.73  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.48/0.73  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.48/0.73  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.48/0.73  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.48/0.73  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.48/0.73  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.48/0.73  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.48/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.73  thf(t6_yellow_1, conjecture,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.73       ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.48/0.73         ( ![B:$i]:
% 0.48/0.73           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.48/0.73             ( ![C:$i]:
% 0.48/0.73               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.48/0.73                 ( r1_tarski @
% 0.48/0.73                   ( k2_xboole_0 @ B @ C ) @ 
% 0.48/0.73                   ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.48/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.73    (~( ![A:$i]:
% 0.48/0.73        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.73          ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.48/0.73            ( ![B:$i]:
% 0.48/0.73              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.48/0.73                ( ![C:$i]:
% 0.48/0.73                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.48/0.73                    ( r1_tarski @
% 0.48/0.73                      ( k2_xboole_0 @ B @ C ) @ 
% 0.48/0.73                      ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.48/0.73    inference('cnf.neg', [status(esa)], [t6_yellow_1])).
% 0.48/0.73  thf('0', plain,
% 0.48/0.73      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf(t1_yellow_1, axiom,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.48/0.73       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.48/0.73  thf('1', plain, (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('2', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.48/0.73  thf('3', plain,
% 0.48/0.73      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('4', plain, (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('5', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.48/0.73  thf('6', plain, (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf(dt_k10_lattice3, axiom,
% 0.48/0.73    (![A:$i,B:$i,C:$i]:
% 0.48/0.73     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.48/0.73         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.73       ( m1_subset_1 @ ( k10_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.48/0.73  thf('7', plain,
% 0.48/0.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.48/0.73          | ~ (l1_orders_2 @ X8)
% 0.48/0.73          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.48/0.73          | (m1_subset_1 @ (k10_lattice3 @ X8 @ X7 @ X9) @ (u1_struct_0 @ X8)))),
% 0.48/0.73      inference('cnf', [status(esa)], [dt_k10_lattice3])).
% 0.48/0.73  thf('8', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.48/0.73          | (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.48/0.73             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.48/0.73          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.73  thf('9', plain, (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('10', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf(dt_k2_yellow_1, axiom,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.48/0.73       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.48/0.73  thf('11', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.48/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.48/0.73  thf('12', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.48/0.73          | (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ X0))),
% 0.48/0.73      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.48/0.73  thf('13', plain,
% 0.48/0.73      (![X0 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.48/0.73          | (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.48/0.73             sk_A))),
% 0.48/0.73      inference('sup-', [status(thm)], ['5', '12'])).
% 0.48/0.73  thf('14', plain,
% 0.48/0.73      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.48/0.73        sk_A)),
% 0.48/0.73      inference('sup-', [status(thm)], ['2', '13'])).
% 0.48/0.73  thf('15', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf(l26_lattice3, axiom,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.48/0.73         ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.48/0.73       ( ![B:$i]:
% 0.48/0.73         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.73           ( ![C:$i]:
% 0.48/0.73             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.73               ( ![D:$i]:
% 0.48/0.73                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.73                   ( ( ( D ) = ( k10_lattice3 @ A @ B @ C ) ) <=>
% 0.48/0.73                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.48/0.73                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.48/0.73                       ( ![E:$i]:
% 0.48/0.73                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.73                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.48/0.73                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.48/0.73                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.73  thf('16', plain,
% 0.48/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.48/0.73          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.48/0.73          | ((X12) != (k10_lattice3 @ X11 @ X10 @ X13))
% 0.48/0.73          | (r1_orders_2 @ X11 @ X13 @ X12)
% 0.48/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.48/0.73          | ~ (l1_orders_2 @ X11)
% 0.48/0.73          | ~ (v1_lattice3 @ X11)
% 0.48/0.73          | ~ (v5_orders_2 @ X11)
% 0.48/0.73          | (v2_struct_0 @ X11))),
% 0.48/0.73      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.48/0.73  thf('17', plain,
% 0.48/0.73      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.48/0.73         ((v2_struct_0 @ X11)
% 0.48/0.73          | ~ (v5_orders_2 @ X11)
% 0.48/0.73          | ~ (v1_lattice3 @ X11)
% 0.48/0.73          | ~ (l1_orders_2 @ X11)
% 0.48/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.48/0.73          | (r1_orders_2 @ X11 @ X13 @ (k10_lattice3 @ X11 @ X10 @ X13))
% 0.48/0.73          | ~ (m1_subset_1 @ (k10_lattice3 @ X11 @ X10 @ X13) @ 
% 0.48/0.73               (u1_struct_0 @ X11))
% 0.48/0.73          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11)))),
% 0.48/0.73      inference('simplify', [status(thm)], ['16'])).
% 0.48/0.73  thf('18', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.48/0.73          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))
% 0.48/0.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.48/0.73          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('sup-', [status(thm)], ['15', '17'])).
% 0.48/0.73  thf('19', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('20', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('21', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.48/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.48/0.73  thf(fc5_yellow_1, axiom,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.48/0.73       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.48/0.73       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.48/0.73       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.48/0.73  thf('22', plain, (![X20 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X20))),
% 0.48/0.73      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.48/0.73  thf('23', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ X0)
% 0.48/0.73          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))
% 0.48/0.73          | ~ (m1_subset_1 @ X1 @ X0)
% 0.48/0.73          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.48/0.73  thf('24', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.48/0.73        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.48/0.73      inference('sup-', [status(thm)], ['14', '23'])).
% 0.48/0.73  thf('25', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('26', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.48/0.73  thf('27', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.48/0.73  thf('28', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.48/0.73      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.48/0.73  thf('29', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf(redefinition_r3_orders_2, axiom,
% 0.48/0.73    (![A:$i,B:$i,C:$i]:
% 0.48/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.48/0.73         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.48/0.73         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.73       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.48/0.73  thf('30', plain,
% 0.48/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.48/0.73          | ~ (l1_orders_2 @ X4)
% 0.48/0.73          | ~ (v3_orders_2 @ X4)
% 0.48/0.73          | (v2_struct_0 @ X4)
% 0.48/0.73          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.48/0.73          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.48/0.73          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.48/0.73      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.48/0.73  thf('31', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.48/0.73          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.48/0.73          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.48/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.73  thf('32', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('33', plain, (![X18 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X18))),
% 0.48/0.73      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.48/0.73  thf('34', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.48/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.48/0.73  thf('35', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.48/0.73          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.48/0.73          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ X0)
% 0.48/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.48/0.73  thf('36', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | ~ (m1_subset_1 @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.48/0.73        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.48/0.73      inference('sup-', [status(thm)], ['28', '35'])).
% 0.48/0.73  thf('37', plain,
% 0.48/0.73      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.48/0.73        sk_A)),
% 0.48/0.73      inference('sup-', [status(thm)], ['2', '13'])).
% 0.48/0.73  thf('38', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.48/0.73  thf('39', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.48/0.73      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.48/0.73  thf('40', plain,
% 0.48/0.73      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.48/0.73         (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.48/0.73      inference('simplify', [status(thm)], ['39'])).
% 0.48/0.73  thf(t3_yellow_1, axiom,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.73       ( ![B:$i]:
% 0.48/0.73         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.48/0.73           ( ![C:$i]:
% 0.48/0.73             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.48/0.73               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.48/0.73                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.48/0.73  thf('41', plain,
% 0.48/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ (k2_yellow_1 @ X24)))
% 0.48/0.73          | ~ (r3_orders_2 @ (k2_yellow_1 @ X24) @ X23 @ X25)
% 0.48/0.73          | (r1_tarski @ X23 @ X25)
% 0.48/0.73          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k2_yellow_1 @ X24)))
% 0.48/0.73          | (v1_xboole_0 @ X24))),
% 0.48/0.73      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.48/0.73  thf('42', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('43', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('44', plain,
% 0.48/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X23 @ X24)
% 0.48/0.73          | ~ (r3_orders_2 @ (k2_yellow_1 @ X24) @ X23 @ X25)
% 0.48/0.73          | (r1_tarski @ X23 @ X25)
% 0.48/0.73          | ~ (m1_subset_1 @ X25 @ X24)
% 0.48/0.73          | (v1_xboole_0 @ X24))),
% 0.48/0.73      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.48/0.73  thf('45', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (v1_xboole_0 @ sk_A)
% 0.48/0.73        | ~ (m1_subset_1 @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.48/0.73        | (r1_tarski @ sk_C @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.48/0.73      inference('sup-', [status(thm)], ['40', '44'])).
% 0.48/0.73  thf('46', plain,
% 0.48/0.73      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.48/0.73        sk_A)),
% 0.48/0.73      inference('sup-', [status(thm)], ['2', '13'])).
% 0.48/0.73  thf('47', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.48/0.73  thf('48', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (v1_xboole_0 @ sk_A)
% 0.48/0.73        | (r1_tarski @ sk_C @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.48/0.73      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.48/0.73  thf('49', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('50', plain,
% 0.48/0.73      (((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.48/0.73      inference('clc', [status(thm)], ['48', '49'])).
% 0.48/0.73  thf('51', plain,
% 0.48/0.73      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.48/0.73        sk_A)),
% 0.48/0.73      inference('sup-', [status(thm)], ['2', '13'])).
% 0.48/0.73  thf('52', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('53', plain,
% 0.48/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.48/0.73          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.48/0.73          | ((X12) != (k10_lattice3 @ X11 @ X10 @ X13))
% 0.48/0.73          | (r1_orders_2 @ X11 @ X10 @ X12)
% 0.48/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.48/0.73          | ~ (l1_orders_2 @ X11)
% 0.48/0.73          | ~ (v1_lattice3 @ X11)
% 0.48/0.73          | ~ (v5_orders_2 @ X11)
% 0.48/0.73          | (v2_struct_0 @ X11))),
% 0.48/0.73      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.48/0.73  thf('54', plain,
% 0.48/0.73      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.48/0.73         ((v2_struct_0 @ X11)
% 0.48/0.73          | ~ (v5_orders_2 @ X11)
% 0.48/0.73          | ~ (v1_lattice3 @ X11)
% 0.48/0.73          | ~ (l1_orders_2 @ X11)
% 0.48/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.48/0.73          | (r1_orders_2 @ X11 @ X10 @ (k10_lattice3 @ X11 @ X10 @ X13))
% 0.48/0.73          | ~ (m1_subset_1 @ (k10_lattice3 @ X11 @ X10 @ X13) @ 
% 0.48/0.73               (u1_struct_0 @ X11))
% 0.48/0.73          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11)))),
% 0.48/0.73      inference('simplify', [status(thm)], ['53'])).
% 0.48/0.73  thf('55', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.48/0.73          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))
% 0.48/0.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.48/0.73          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('sup-', [status(thm)], ['52', '54'])).
% 0.48/0.73  thf('56', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('57', plain,
% 0.48/0.73      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.48/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.48/0.73  thf('58', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.48/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.48/0.73  thf('59', plain, (![X20 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X20))),
% 0.48/0.73      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.48/0.73  thf('60', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ X0)
% 0.48/0.73          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))
% 0.48/0.73          | ~ (m1_subset_1 @ X1 @ X0)
% 0.48/0.73          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.48/0.73  thf('61', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.48/0.73        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.48/0.73      inference('sup-', [status(thm)], ['51', '60'])).
% 0.48/0.73  thf('62', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('63', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.48/0.73  thf('64', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.48/0.73  thf('65', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.48/0.73      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.48/0.73  thf('66', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.48/0.73          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.48/0.73          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.48/0.73          | ~ (m1_subset_1 @ X2 @ X0)
% 0.48/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.48/0.73  thf('67', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | ~ (m1_subset_1 @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.48/0.73        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.48/0.73      inference('sup-', [status(thm)], ['65', '66'])).
% 0.48/0.73  thf('68', plain,
% 0.48/0.73      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.48/0.73        sk_A)),
% 0.48/0.73      inference('sup-', [status(thm)], ['2', '13'])).
% 0.48/0.73  thf('69', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.48/0.73  thf('70', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.48/0.73      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.48/0.73  thf('71', plain,
% 0.48/0.73      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.48/0.73         (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.48/0.73      inference('simplify', [status(thm)], ['70'])).
% 0.48/0.73  thf('72', plain,
% 0.48/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.48/0.73         (~ (m1_subset_1 @ X23 @ X24)
% 0.48/0.73          | ~ (r3_orders_2 @ (k2_yellow_1 @ X24) @ X23 @ X25)
% 0.48/0.73          | (r1_tarski @ X23 @ X25)
% 0.48/0.73          | ~ (m1_subset_1 @ X25 @ X24)
% 0.48/0.73          | (v1_xboole_0 @ X24))),
% 0.48/0.73      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.48/0.73  thf('73', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (v1_xboole_0 @ sk_A)
% 0.48/0.73        | ~ (m1_subset_1 @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.48/0.73        | (r1_tarski @ sk_B @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.48/0.73      inference('sup-', [status(thm)], ['71', '72'])).
% 0.48/0.73  thf('74', plain,
% 0.48/0.73      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.48/0.73        sk_A)),
% 0.48/0.73      inference('sup-', [status(thm)], ['2', '13'])).
% 0.48/0.73  thf('75', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.48/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.48/0.73  thf('76', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (v1_xboole_0 @ sk_A)
% 0.48/0.73        | (r1_tarski @ sk_B @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.48/0.73      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.48/0.73  thf('77', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('78', plain,
% 0.48/0.73      (((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.48/0.73      inference('clc', [status(thm)], ['76', '77'])).
% 0.48/0.73  thf(t8_xboole_1, axiom,
% 0.48/0.73    (![A:$i,B:$i,C:$i]:
% 0.48/0.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.48/0.73       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.48/0.73  thf('79', plain,
% 0.48/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.73         (~ (r1_tarski @ X0 @ X1)
% 0.48/0.73          | ~ (r1_tarski @ X2 @ X1)
% 0.48/0.73          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.48/0.73      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.48/0.73  thf('80', plain,
% 0.48/0.73      (![X0 : $i]:
% 0.48/0.73         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 0.48/0.73             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73          | ~ (r1_tarski @ X0 @ 
% 0.48/0.73               (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.48/0.73      inference('sup-', [status(thm)], ['78', '79'])).
% 0.48/0.73  thf('81', plain,
% 0.48/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.48/0.73        | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.48/0.73           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.48/0.73      inference('sup-', [status(thm)], ['50', '80'])).
% 0.48/0.73  thf('82', plain,
% 0.48/0.73      (((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.48/0.73         (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.48/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.48/0.73      inference('simplify', [status(thm)], ['81'])).
% 0.48/0.73  thf('83', plain,
% 0.48/0.73      (~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.48/0.73          (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('84', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.48/0.73      inference('clc', [status(thm)], ['82', '83'])).
% 0.48/0.73  thf('85', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.48/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.48/0.73  thf(cc1_lattice3, axiom,
% 0.48/0.73    (![A:$i]:
% 0.48/0.73     ( ( l1_orders_2 @ A ) =>
% 0.48/0.73       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.48/0.73  thf('86', plain,
% 0.48/0.73      (![X6 : $i]:
% 0.48/0.73         (~ (v1_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.48/0.73      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.48/0.73  thf('87', plain,
% 0.48/0.73      (![X0 : $i]:
% 0.48/0.73         (~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.48/0.73          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.48/0.73      inference('sup-', [status(thm)], ['85', '86'])).
% 0.48/0.73  thf('88', plain, (~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.48/0.73      inference('sup-', [status(thm)], ['84', '87'])).
% 0.48/0.73  thf('89', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.48/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.73  thf('90', plain, ($false), inference('demod', [status(thm)], ['88', '89'])).
% 0.48/0.73  
% 0.48/0.73  % SZS output end Refutation
% 0.48/0.73  
% 0.48/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
