%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BRgK5QnzSn

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:05 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 920 expanded)
%              Number of leaves         :   34 ( 320 expanded)
%              Depth                    :   18
%              Number of atoms          : 1447 (11371 expanded)
%              Number of equality atoms :   44 ( 510 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k13_lattice3 @ X10 @ X9 @ X11 )
        = ( k10_lattice3 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X21: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

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

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( X17
       != ( k13_lattice3 @ X16 @ X15 @ X18 ) )
      | ( r1_orders_2 @ X16 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t22_yellow_0])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( v5_orders_2 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( r1_orders_2 @ X16 @ X18 @ ( k13_lattice3 @ X16 @ X15 @ X18 ) )
      | ~ ( m1_subset_1 @ ( k13_lattice3 @ X16 @ X15 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('24',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k13_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v1_lattice3 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k13_lattice3 @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k13_lattice3])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('29',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('30',plain,(
    ! [X25: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('31',plain,(
    ! [X21: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('43',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t13_lattice3,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k10_lattice3 @ A @ B @ C )
                = ( k10_lattice3 @ A @ C @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k10_lattice3 @ X13 @ X12 @ X14 )
        = ( k10_lattice3 @ X13 @ X14 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t13_lattice3])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X25: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('48',plain,(
    ! [X21: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('49',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,
    ( ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['40','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','54'])).

thf('56',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('58',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('59',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('61',plain,(
    ! [X21: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('62',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X25: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('64',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','55','56','57','58','59','60','61','62','63'])).

thf('65',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
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

thf('66',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('69',plain,(
    ! [X23: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('70',plain,(
    ! [X21: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','54'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('75',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X30 ) @ X29 @ X31 )
      | ( r1_tarski @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) ) )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('77',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('78',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('79',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X30 ) @ X29 @ X31 )
      | ( r1_tarski @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','54'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('83',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('84',plain,(
    ! [X26: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X26 ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('85',plain,
    ( ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['40','53'])).

thf('89',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( v5_orders_2 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( r1_orders_2 @ X16 @ X18 @ ( k13_lattice3 @ X16 @ X15 @ X18 ) )
      | ~ ( m1_subset_1 @ ( k13_lattice3 @ X16 @ X15 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('92',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','54'])).

thf('93',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('95',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['40','53'])).

thf('96',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('98',plain,(
    ! [X21: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('99',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X25: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('101',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95','96','97','98','99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('103',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','54'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('106',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X30 ) @ X29 @ X31 )
      | ( r1_tarski @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('108',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','54'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('111',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X26: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X26 ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('113',plain,
    ( ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['113','114'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['87','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['0','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BRgK5QnzSn
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:10:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 243 iterations in 0.185s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.46/0.63  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.46/0.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.63  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.46/0.63  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.46/0.63  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.46/0.63  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.46/0.63  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.46/0.63  thf(t6_yellow_1, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.63       ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.46/0.63         ( ![B:$i]:
% 0.46/0.63           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.63             ( ![C:$i]:
% 0.46/0.63               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.63                 ( r1_tarski @
% 0.46/0.63                   ( k2_xboole_0 @ B @ C ) @ 
% 0.46/0.63                   ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.63          ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.46/0.63            ( ![B:$i]:
% 0.46/0.63              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.63                ( ![C:$i]:
% 0.46/0.63                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.63                    ( r1_tarski @
% 0.46/0.63                      ( k2_xboole_0 @ B @ C ) @ 
% 0.46/0.63                      ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t6_yellow_1])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.46/0.63          (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t1_yellow_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.46/0.63       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.63  thf('2', plain, (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('5', plain, (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf('6', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('7', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('8', plain, (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf(redefinition_k13_lattice3, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.46/0.63          | ~ (l1_orders_2 @ X10)
% 0.46/0.63          | ~ (v1_lattice3 @ X10)
% 0.46/0.63          | ~ (v5_orders_2 @ X10)
% 0.46/0.63          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.46/0.63          | ((k13_lattice3 @ X10 @ X9 @ X11) = (k10_lattice3 @ X10 @ X9 @ X11)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.63          | ((k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.46/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.63          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.63          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.46/0.63          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf(fc5_yellow_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.63       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.63       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.63       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.46/0.63  thf('12', plain, (![X25 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X25))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.63  thf(dt_k2_yellow_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.63       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.46/0.63  thf('13', plain, (![X21 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X21))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.63          | ((k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.46/0.63          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.63          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.63          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.63          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['6', '15'])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.46/0.63         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '16'])).
% 0.46/0.63  thf(t22_yellow_0, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63               ( ![D:$i]:
% 0.46/0.63                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63                   ( ( ( D ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.46/0.63                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.46/0.63                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.46/0.63                       ( ![E:$i]:
% 0.46/0.63                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.46/0.63                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.46/0.63                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.46/0.63          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.46/0.63          | ((X17) != (k13_lattice3 @ X16 @ X15 @ X18))
% 0.46/0.63          | (r1_orders_2 @ X16 @ X18 @ X17)
% 0.46/0.63          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.46/0.63          | ~ (l1_orders_2 @ X16)
% 0.46/0.63          | ~ (v1_lattice3 @ X16)
% 0.46/0.63          | ~ (v5_orders_2 @ X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t22_yellow_0])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.46/0.63         (~ (v5_orders_2 @ X16)
% 0.46/0.63          | ~ (v1_lattice3 @ X16)
% 0.46/0.63          | ~ (l1_orders_2 @ X16)
% 0.46/0.63          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.46/0.63          | (r1_orders_2 @ X16 @ X18 @ (k13_lattice3 @ X16 @ X15 @ X18))
% 0.46/0.63          | ~ (m1_subset_1 @ (k13_lattice3 @ X16 @ X15 @ X18) @ 
% 0.46/0.63               (u1_struct_0 @ X16))
% 0.46/0.63          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.63           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.63        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.63        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.46/0.63           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.46/0.63        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.63        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.46/0.63        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.46/0.63        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['17', '19'])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf('22', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('23', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('24', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf(dt_k13_lattice3, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63       ( m1_subset_1 @ ( k13_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.46/0.63          | ~ (l1_orders_2 @ X7)
% 0.46/0.63          | ~ (v1_lattice3 @ X7)
% 0.46/0.63          | ~ (v5_orders_2 @ X7)
% 0.46/0.63          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.46/0.63          | (m1_subset_1 @ (k13_lattice3 @ X7 @ X6 @ X8) @ (u1_struct_0 @ X7)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k13_lattice3])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.63          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.46/0.63             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.63          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.63          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.46/0.63          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf('30', plain, (![X25 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X25))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.63  thf('31', plain, (![X21 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X21))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.63          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.46/0.63          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.63          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.63          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0) @ 
% 0.46/0.63             sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['24', '32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.63          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B) @ 
% 0.46/0.63             sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['23', '33'])).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.46/0.63        sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '34'])).
% 0.46/0.63  thf('36', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('37', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.63          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '14'])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.63          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.46/0.63         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['36', '39'])).
% 0.46/0.63  thf('41', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('42', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('43', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf(t13_lattice3, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63               ( ( k10_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.46/0.63          | ((k10_lattice3 @ X13 @ X12 @ X14)
% 0.46/0.63              = (k10_lattice3 @ X13 @ X14 @ X12))
% 0.46/0.63          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.46/0.63          | ~ (l1_orders_2 @ X13)
% 0.46/0.63          | ~ (v1_lattice3 @ X13)
% 0.46/0.63          | ~ (v5_orders_2 @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [t13_lattice3])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.63          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.63          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.46/0.63          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.63          | ((k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.63  thf('47', plain, (![X25 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X25))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.63  thf('48', plain, (![X21 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X21))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.63          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.63          | ((k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)))),
% 0.46/0.63      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (((k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.46/0.63            = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['43', '50'])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.63          | ((k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 0.46/0.63              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['42', '51'])).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      (((k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.46/0.63         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['41', '52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.46/0.64         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.64        sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '54'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf('57', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.46/0.64         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '16'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf('60', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('61', plain, (![X21 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.64  thf('62', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('63', plain, (![X25 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.46/0.64        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['20', '21', '55', '56', '57', '58', '59', '60', '61', '62', 
% 0.46/0.64                 '63'])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf(redefinition_r3_orders_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.64         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.46/0.64          | ~ (l1_orders_2 @ X4)
% 0.46/0.64          | ~ (v3_orders_2 @ X4)
% 0.46/0.64          | (v2_struct_0 @ X4)
% 0.46/0.64          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.46/0.64          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.46/0.64          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.64          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.64          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.64          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.46/0.64          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.64          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf('69', plain, (![X23 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.64  thf('70', plain, (![X21 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.64          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.64          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.64          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | ~ (m1_subset_1 @ 
% 0.46/0.64             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.46/0.64        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['64', '71'])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.64        sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '54'])).
% 0.46/0.64  thf('74', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.46/0.64  thf(t3_yellow_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.64               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.46/0.64                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ (k2_yellow_1 @ X30)))
% 0.46/0.64          | ~ (r3_orders_2 @ (k2_yellow_1 @ X30) @ X29 @ X31)
% 0.46/0.64          | (r1_tarski @ X29 @ X31)
% 0.46/0.64          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ (k2_yellow_1 @ X30)))
% 0.46/0.64          | (v1_xboole_0 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X29 @ X30)
% 0.46/0.64          | ~ (r3_orders_2 @ (k2_yellow_1 @ X30) @ X29 @ X31)
% 0.46/0.64          | (r1_tarski @ X29 @ X31)
% 0.46/0.64          | ~ (m1_subset_1 @ X31 @ X30)
% 0.46/0.64          | (v1_xboole_0 @ X30))),
% 0.46/0.64      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | ~ (m1_subset_1 @ 
% 0.46/0.64             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.46/0.64        | (r1_tarski @ sk_C @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['75', '79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.64        sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '54'])).
% 0.46/0.64  thf('82', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (r1_tarski @ sk_C @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.46/0.64  thf(fc6_yellow_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.64       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.46/0.64         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         (~ (v2_struct_0 @ (k2_yellow_1 @ X26)) | (v1_xboole_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.46/0.64        | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['83', '84'])).
% 0.46/0.64  thf('86', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      ((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.46/0.64         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '53'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.46/0.64         (~ (v5_orders_2 @ X16)
% 0.46/0.64          | ~ (v1_lattice3 @ X16)
% 0.46/0.64          | ~ (l1_orders_2 @ X16)
% 0.46/0.64          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.46/0.64          | (r1_orders_2 @ X16 @ X18 @ (k13_lattice3 @ X16 @ X15 @ X18))
% 0.46/0.64          | ~ (m1_subset_1 @ (k13_lattice3 @ X16 @ X15 @ X18) @ 
% 0.46/0.64               (u1_struct_0 @ X16))
% 0.46/0.64          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.64           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.64        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.46/0.64           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.64        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.64        sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '54'])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf('94', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.46/0.64         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '53'])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.64  thf('97', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('98', plain, (![X21 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.64  thf('99', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('100', plain, (![X25 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.46/0.64        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['90', '91', '92', '93', '94', '95', '96', '97', '98', '99', 
% 0.46/0.64                 '100'])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.64          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.64          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.64          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | ~ (m1_subset_1 @ 
% 0.46/0.64             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.46/0.64        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.64  thf('104', plain,
% 0.46/0.64      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.64        sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '54'])).
% 0.46/0.64  thf('105', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X29 @ X30)
% 0.46/0.64          | ~ (r3_orders_2 @ (k2_yellow_1 @ X30) @ X29 @ X31)
% 0.46/0.64          | (r1_tarski @ X29 @ X31)
% 0.46/0.64          | ~ (m1_subset_1 @ X31 @ X30)
% 0.46/0.64          | (v1_xboole_0 @ X30))),
% 0.46/0.64      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | ~ (m1_subset_1 @ 
% 0.46/0.64             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.46/0.64        | (r1_tarski @ sk_B @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['106', '107'])).
% 0.46/0.64  thf('109', plain,
% 0.46/0.64      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.64        sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '54'])).
% 0.46/0.64  thf('110', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('111', plain,
% 0.46/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (r1_tarski @ sk_B @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         (~ (v2_struct_0 @ (k2_yellow_1 @ X26)) | (v1_xboole_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.46/0.64  thf('113', plain,
% 0.46/0.64      (((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.46/0.64        | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['111', '112'])).
% 0.46/0.64  thf('114', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('115', plain,
% 0.46/0.64      ((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('clc', [status(thm)], ['113', '114'])).
% 0.46/0.64  thf(t8_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.46/0.64       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.64  thf('116', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.64          | ~ (r1_tarski @ X2 @ X1)
% 0.46/0.64          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.46/0.64  thf('117', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 0.46/0.64           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.46/0.64          | ~ (r1_tarski @ X0 @ 
% 0.46/0.64               (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['115', '116'])).
% 0.46/0.64  thf('118', plain,
% 0.46/0.64      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.46/0.64        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['87', '117'])).
% 0.46/0.64  thf('119', plain, ($false), inference('demod', [status(thm)], ['0', '118'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
