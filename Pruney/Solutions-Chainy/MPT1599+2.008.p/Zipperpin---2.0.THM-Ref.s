%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ftZi1zEvVf

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:06 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 340 expanded)
%              Number of leaves         :   31 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          : 1191 (3920 expanded)
%              Number of equality atoms :   20 ( 160 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(t7_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
               => ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) )
         => ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
                 => ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_yellow_1])).

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
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X10 @ X9 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('10',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(l28_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k11_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ D @ B )
                      & ( r1_orders_2 @ A @ D @ C )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ E @ B )
                              & ( r1_orders_2 @ A @ E @ C ) )
                           => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( X14
       != ( k11_lattice3 @ X13 @ X12 @ X15 ) )
      | ( r1_orders_2 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('17',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ ( k11_lattice3 @ X13 @ X12 @ X15 ) @ X15 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X13 @ X12 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('21',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('28',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( r3_orders_2 @ X6 @ X5 @ X7 )
      | ~ ( r1_orders_2 @ X6 @ X5 @ X7 ) ) ),
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
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('33',plain,(
    ! [X20: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('34',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
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
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('38',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('39',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X26 ) @ X25 @ X27 )
      | ( r1_tarski @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('42',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('44',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X26 ) @ X25 @ X27 )
      | ( r1_tarski @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('47',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('48',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('52',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( X14
       != ( k11_lattice3 @ X13 @ X12 @ X15 ) )
      | ( r1_orders_2 @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ ( k11_lattice3 @ X13 @ X12 @ X15 ) @ X12 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X13 @ X12 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('57',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('58',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('59',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
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
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('69',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('70',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X26 ) @ X25 @ X27 )
      | ( r1_tarski @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('73',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('75',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['2','13'])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','80'])).

thf('82',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('86',plain,(
    ! [X8: $i] :
      ( ~ ( v2_lattice3 @ X8 )
      | ~ ( v2_struct_0 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ftZi1zEvVf
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 227 iterations in 0.308s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.59/0.77  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.59/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.59/0.77  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.59/0.77  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.59/0.77  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.59/0.77  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.59/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.77  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.59/0.77  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.59/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.77  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.59/0.77  thf(t7_yellow_1, conjecture,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.59/0.77         ( ![B:$i]:
% 0.59/0.77           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.77             ( ![C:$i]:
% 0.59/0.77               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.77                 ( r1_tarski @
% 0.59/0.77                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.59/0.77                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i]:
% 0.59/0.77        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.59/0.77            ( ![B:$i]:
% 0.59/0.77              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.77                ( ![C:$i]:
% 0.59/0.77                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.77                    ( r1_tarski @
% 0.59/0.77                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.59/0.77                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t1_yellow_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.59/0.77       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.59/0.77  thf('1', plain, (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('2', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('4', plain, (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('5', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('6', plain, (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf(dt_k11_lattice3, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.59/0.77         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.77       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.59/0.77          | ~ (l1_orders_2 @ X10)
% 0.59/0.77          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.59/0.77          | (m1_subset_1 @ (k11_lattice3 @ X10 @ X9 @ X11) @ 
% 0.59/0.77             (u1_struct_0 @ X10)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X1 @ X0)
% 0.59/0.77          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.59/0.77             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.59/0.77          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.77  thf('9', plain, (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf(dt_k2_yellow_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.59/0.77       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.59/0.77  thf('11', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X1 @ X0)
% 0.59/0.77          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.59/0.77          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.59/0.77             sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['5', '12'])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77        sk_A)),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '13'])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf(l28_lattice3, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.59/0.77         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.77               ( ![D:$i]:
% 0.59/0.77                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.77                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 0.59/0.77                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.59/0.77                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.59/0.77                       ( ![E:$i]:
% 0.59/0.77                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.77                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.59/0.77                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.59/0.77                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.59/0.77          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.59/0.77          | ((X14) != (k11_lattice3 @ X13 @ X12 @ X15))
% 0.59/0.77          | (r1_orders_2 @ X13 @ X14 @ X15)
% 0.59/0.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.59/0.77          | ~ (l1_orders_2 @ X13)
% 0.59/0.77          | ~ (v2_lattice3 @ X13)
% 0.59/0.77          | ~ (v5_orders_2 @ X13)
% 0.59/0.77          | (v2_struct_0 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.59/0.77         ((v2_struct_0 @ X13)
% 0.59/0.77          | ~ (v5_orders_2 @ X13)
% 0.59/0.77          | ~ (v2_lattice3 @ X13)
% 0.59/0.77          | ~ (l1_orders_2 @ X13)
% 0.59/0.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.59/0.77          | (r1_orders_2 @ X13 @ (k11_lattice3 @ X13 @ X12 @ X15) @ X15)
% 0.59/0.77          | ~ (m1_subset_1 @ (k11_lattice3 @ X13 @ X12 @ X15) @ 
% 0.59/0.77               (u1_struct_0 @ X13))
% 0.59/0.77          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['16'])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.59/0.77          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.59/0.77             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X1)
% 0.59/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.59/0.77          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['15', '17'])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('21', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.77  thf(fc5_yellow_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.59/0.77       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.59/0.77       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.59/0.77       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.59/0.77  thf('22', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ X0)
% 0.59/0.77          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.59/0.77             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X1)
% 0.59/0.77          | ~ (m1_subset_1 @ X1 @ X0)
% 0.59/0.77          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.59/0.77        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['14', '23'])).
% 0.59/0.77  thf('25', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('26', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf('27', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf(redefinition_r3_orders_2, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.77         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.59/0.77         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.77       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.59/0.77          | ~ (l1_orders_2 @ X6)
% 0.59/0.77          | ~ (v3_orders_2 @ X6)
% 0.59/0.77          | (v2_struct_0 @ X6)
% 0.59/0.77          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.59/0.77          | (r3_orders_2 @ X6 @ X5 @ X7)
% 0.59/0.77          | ~ (r1_orders_2 @ X6 @ X5 @ X7))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X1 @ X0)
% 0.59/0.77          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.59/0.77          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.59/0.77          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('33', plain, (![X20 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X20))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.59/0.77  thf('34', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.77  thf('35', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X1 @ X0)
% 0.59/0.77          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.59/0.77          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ X0)
% 0.59/0.77          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.59/0.77  thf('36', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.59/0.77        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.59/0.77        | ~ (m1_subset_1 @ 
% 0.59/0.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['28', '35'])).
% 0.59/0.77  thf('37', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf('38', plain,
% 0.59/0.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77        sk_A)),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '13'])).
% 0.59/0.77  thf('39', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.59/0.77  thf('40', plain,
% 0.59/0.77      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['39'])).
% 0.59/0.77  thf(t3_yellow_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.77               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.59/0.77                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k2_yellow_1 @ X26)))
% 0.59/0.77          | ~ (r3_orders_2 @ (k2_yellow_1 @ X26) @ X25 @ X27)
% 0.59/0.77          | (r1_tarski @ X25 @ X27)
% 0.59/0.77          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X26)))
% 0.59/0.77          | (v1_xboole_0 @ X26))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.59/0.77  thf('42', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('43', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('44', plain,
% 0.59/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X25 @ X26)
% 0.59/0.77          | ~ (r3_orders_2 @ (k2_yellow_1 @ X26) @ X25 @ X27)
% 0.59/0.77          | (r1_tarski @ X25 @ X27)
% 0.59/0.77          | ~ (m1_subset_1 @ X27 @ X26)
% 0.59/0.77          | (v1_xboole_0 @ X26))),
% 0.59/0.77      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.59/0.77  thf('45', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.59/0.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77           sk_C)
% 0.59/0.77        | ~ (m1_subset_1 @ 
% 0.59/0.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['40', '44'])).
% 0.59/0.77  thf('46', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf('47', plain,
% 0.59/0.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77        sk_A)),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '13'])).
% 0.59/0.77  thf('48', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77           sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.59/0.77  thf('49', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('50', plain,
% 0.59/0.77      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.77      inference('clc', [status(thm)], ['48', '49'])).
% 0.59/0.77  thf('51', plain,
% 0.59/0.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77        sk_A)),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '13'])).
% 0.59/0.77  thf('52', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('53', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.59/0.77          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.59/0.77          | ((X14) != (k11_lattice3 @ X13 @ X12 @ X15))
% 0.59/0.77          | (r1_orders_2 @ X13 @ X14 @ X12)
% 0.59/0.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.59/0.77          | ~ (l1_orders_2 @ X13)
% 0.59/0.77          | ~ (v2_lattice3 @ X13)
% 0.59/0.77          | ~ (v5_orders_2 @ X13)
% 0.59/0.77          | (v2_struct_0 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.59/0.77  thf('54', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.59/0.77         ((v2_struct_0 @ X13)
% 0.59/0.77          | ~ (v5_orders_2 @ X13)
% 0.59/0.77          | ~ (v2_lattice3 @ X13)
% 0.59/0.77          | ~ (l1_orders_2 @ X13)
% 0.59/0.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.59/0.77          | (r1_orders_2 @ X13 @ (k11_lattice3 @ X13 @ X12 @ X15) @ X12)
% 0.59/0.77          | ~ (m1_subset_1 @ (k11_lattice3 @ X13 @ X12 @ X15) @ 
% 0.59/0.77               (u1_struct_0 @ X13))
% 0.59/0.77          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.77  thf('55', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.59/0.77          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.59/0.77             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X2)
% 0.59/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.59/0.77          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['52', '54'])).
% 0.59/0.77  thf('56', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('57', plain,
% 0.59/0.77      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.59/0.77      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.59/0.77  thf('58', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.77  thf('59', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.59/0.77  thf('60', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ X0)
% 0.59/0.77          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.59/0.77             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X2)
% 0.59/0.77          | ~ (m1_subset_1 @ X1 @ X0)
% 0.59/0.77          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.59/0.77  thf('61', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.59/0.77        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['51', '60'])).
% 0.59/0.77  thf('62', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('63', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf('64', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('65', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.59/0.77  thf('66', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X1 @ X0)
% 0.59/0.77          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.59/0.77          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ X0)
% 0.59/0.77          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.59/0.77  thf('67', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.59/0.77        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.59/0.77        | ~ (m1_subset_1 @ 
% 0.59/0.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.77  thf('68', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('69', plain,
% 0.59/0.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77        sk_A)),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '13'])).
% 0.59/0.77  thf('70', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.59/0.77  thf('71', plain,
% 0.59/0.77      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.77         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['70'])).
% 0.59/0.77  thf('72', plain,
% 0.59/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X25 @ X26)
% 0.59/0.77          | ~ (r3_orders_2 @ (k2_yellow_1 @ X26) @ X25 @ X27)
% 0.59/0.77          | (r1_tarski @ X25 @ X27)
% 0.59/0.77          | ~ (m1_subset_1 @ X27 @ X26)
% 0.59/0.77          | (v1_xboole_0 @ X26))),
% 0.59/0.77      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.59/0.77  thf('73', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.59/0.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77           sk_B)
% 0.59/0.77        | ~ (m1_subset_1 @ 
% 0.59/0.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['71', '72'])).
% 0.59/0.77  thf('74', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('75', plain,
% 0.59/0.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77        sk_A)),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '13'])).
% 0.59/0.77  thf('76', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77           sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.59/0.77  thf('77', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('78', plain,
% 0.59/0.77      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.77      inference('clc', [status(thm)], ['76', '77'])).
% 0.59/0.77  thf(t19_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.59/0.77       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('79', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X0 @ X1)
% 0.59/0.77          | ~ (r1_tarski @ X0 @ X2)
% 0.59/0.77          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.59/0.77  thf('80', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77             (k3_xboole_0 @ sk_B @ X0))
% 0.59/0.77          | ~ (r1_tarski @ 
% 0.59/0.77               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['78', '79'])).
% 0.59/0.77  thf('81', plain,
% 0.59/0.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77           (k3_xboole_0 @ sk_B @ sk_C))
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['50', '80'])).
% 0.59/0.77  thf('82', plain,
% 0.59/0.77      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77         (k3_xboole_0 @ sk_B @ sk_C))
% 0.59/0.77        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['81'])).
% 0.59/0.77  thf('83', plain,
% 0.59/0.77      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.77          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('84', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.77      inference('clc', [status(thm)], ['82', '83'])).
% 0.59/0.77  thf('85', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.77  thf(cc2_lattice3, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( l1_orders_2 @ A ) =>
% 0.59/0.77       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.59/0.77  thf('86', plain,
% 0.59/0.77      (![X8 : $i]:
% 0.59/0.77         (~ (v2_lattice3 @ X8) | ~ (v2_struct_0 @ X8) | ~ (l1_orders_2 @ X8))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.59/0.77  thf('87', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.59/0.77          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['85', '86'])).
% 0.59/0.77  thf('88', plain, (~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['84', '87'])).
% 0.59/0.77  thf('89', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('90', plain, ($false), inference('demod', [status(thm)], ['88', '89'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
