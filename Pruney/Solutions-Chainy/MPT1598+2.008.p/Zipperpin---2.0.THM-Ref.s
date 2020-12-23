%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jTlToiJ6tt

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:05 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 672 expanded)
%              Number of leaves         :   33 ( 240 expanded)
%              Depth                    :   17
%              Number of atoms          : 1266 (8187 expanded)
%              Number of equality atoms :   33 ( 350 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v1_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( ( k13_lattice3 @ X12 @ X11 @ X13 )
        = ( k10_lattice3 @ X12 @ X11 @ X13 ) ) ) ),
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
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X24: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X20: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( X16
       != ( k13_lattice3 @ X15 @ X14 @ X17 ) )
      | ( r1_orders_2 @ X15 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v1_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t22_yellow_0])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v5_orders_2 @ X15 )
      | ~ ( v1_lattice3 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X17 @ ( k13_lattice3 @ X15 @ X14 @ X17 ) )
      | ~ ( m1_subset_1 @ ( k13_lattice3 @ X15 @ X14 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) ) ) ),
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
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('24',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v1_lattice3 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k13_lattice3 @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
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
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('29',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('30',plain,(
    ! [X24: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('31',plain,(
    ! [X20: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
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
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('37',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('40',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('41',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('43',plain,(
    ! [X20: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('44',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X24: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('46',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','37','38','39','40','41','42','43','44','45'])).

thf('47',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
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

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( r3_orders_2 @ X6 @ X5 @ X7 )
      | ~ ( r1_orders_2 @ X6 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('51',plain,(
    ! [X22: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('52',plain,(
    ! [X20: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('57',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('58',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X29 ) @ X28 @ X30 )
      | ( r1_tarski @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('59',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('60',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('61',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X29 ) @ X28 @ X30 )
      | ( r1_tarski @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('66',plain,(
    ! [X25: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X25 ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('67',plain,
    ( ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( X16
       != ( k13_lattice3 @ X15 @ X14 @ X17 ) )
      | ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v1_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t22_yellow_0])).

thf('72',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v5_orders_2 @ X15 )
      | ~ ( v1_lattice3 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X14 @ ( k13_lattice3 @ X15 @ X14 @ X17 ) )
      | ~ ( m1_subset_1 @ ( k13_lattice3 @ X15 @ X14 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('75',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('76',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('78',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('79',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('81',plain,(
    ! [X20: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('82',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X24: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('84',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78','79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('86',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('89',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X29 ) @ X28 @ X30 )
      | ( r1_tarski @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('91',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('94',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X25: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X25 ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('96',plain,
    ( ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['96','97'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['69','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jTlToiJ6tt
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 246 iterations in 0.219s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.45/0.69  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.45/0.69  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.45/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.69  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.45/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.69  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.45/0.69  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.45/0.69  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.69  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.45/0.69  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.45/0.69  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.45/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.69  thf(t6_yellow_1, conjecture,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.69       ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.45/0.69         ( ![B:$i]:
% 0.45/0.69           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.45/0.69             ( ![C:$i]:
% 0.45/0.69               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.45/0.69                 ( r1_tarski @
% 0.45/0.69                   ( k2_xboole_0 @ B @ C ) @ 
% 0.45/0.69                   ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i]:
% 0.45/0.69        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.69          ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.45/0.69            ( ![B:$i]:
% 0.45/0.69              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.45/0.69                ( ![C:$i]:
% 0.45/0.69                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.45/0.69                    ( r1_tarski @
% 0.45/0.69                      ( k2_xboole_0 @ B @ C ) @ 
% 0.45/0.69                      ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t6_yellow_1])).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.45/0.69          (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(t1_yellow_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.45/0.69       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.69  thf('2', plain, (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('5', plain, (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('6', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('7', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('8', plain, (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf(redefinition_k13_lattice3, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.45/0.69         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.69         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.45/0.69          | ~ (l1_orders_2 @ X12)
% 0.45/0.69          | ~ (v1_lattice3 @ X12)
% 0.45/0.69          | ~ (v5_orders_2 @ X12)
% 0.45/0.69          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.45/0.69          | ((k13_lattice3 @ X12 @ X11 @ X13)
% 0.45/0.69              = (k10_lattice3 @ X12 @ X11 @ X13)))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.45/0.69              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.45/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.45/0.69          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.45/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.45/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf(fc5_yellow_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.45/0.69       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.45/0.69       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.45/0.69       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.45/0.69  thf('12', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.45/0.69  thf(dt_k2_yellow_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.45/0.69       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.45/0.69  thf('13', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.45/0.69              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.45/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.45/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.45/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.45/0.69              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 0.45/0.69          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['7', '14'])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.45/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 0.45/0.69              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['6', '15'])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.45/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['3', '16'])).
% 0.45/0.69  thf(t22_yellow_0, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69               ( ![D:$i]:
% 0.45/0.69                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69                   ( ( ( D ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.45/0.69                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.45/0.69                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.45/0.69                       ( ![E:$i]:
% 0.45/0.69                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.45/0.69                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.45/0.69                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ((X16) != (k13_lattice3 @ X15 @ X14 @ X17))
% 0.45/0.69          | (r1_orders_2 @ X15 @ X17 @ X16)
% 0.45/0.69          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (l1_orders_2 @ X15)
% 0.45/0.69          | ~ (v1_lattice3 @ X15)
% 0.45/0.69          | ~ (v5_orders_2 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t22_yellow_0])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.45/0.69         (~ (v5_orders_2 @ X15)
% 0.45/0.69          | ~ (v1_lattice3 @ X15)
% 0.45/0.69          | ~ (l1_orders_2 @ X15)
% 0.45/0.69          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.45/0.69          | (r1_orders_2 @ X15 @ X17 @ (k13_lattice3 @ X15 @ X14 @ X17))
% 0.45/0.69          | ~ (m1_subset_1 @ (k13_lattice3 @ X15 @ X14 @ X17) @ 
% 0.45/0.69               (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      ((~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.45/0.69        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.45/0.69        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.45/0.69           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.45/0.69        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['17', '19'])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('22', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf('23', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('24', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf(dt_k13_lattice3, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.45/0.69         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.69         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69       ( m1_subset_1 @ ( k13_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.45/0.69          | ~ (l1_orders_2 @ X9)
% 0.45/0.69          | ~ (v1_lattice3 @ X9)
% 0.45/0.69          | ~ (v5_orders_2 @ X9)
% 0.45/0.69          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.45/0.69          | (m1_subset_1 @ (k13_lattice3 @ X9 @ X8 @ X10) @ (u1_struct_0 @ X9)))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k13_lattice3])).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.69          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.45/0.69             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.45/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.45/0.69          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.45/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.45/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('30', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.45/0.69  thf('31', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.69          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.45/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.45/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.45/0.69          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0) @ 
% 0.45/0.69             sk_A)
% 0.45/0.69          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['24', '32'])).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.45/0.69          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C) @ 
% 0.45/0.69             sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['23', '33'])).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69        sk_A)),
% 0.45/0.69      inference('sup-', [status(thm)], ['22', '34'])).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.45/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['3', '16'])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69        sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('39', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.45/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['3', '16'])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('42', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('43', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.45/0.69  thf('44', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('45', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.45/0.69        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)],
% 0.45/0.69                ['20', '21', '37', '38', '39', '40', '41', '42', '43', '44', 
% 0.45/0.69                 '45'])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf(redefinition_r3_orders_2, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.69         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.69         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.45/0.69          | ~ (l1_orders_2 @ X6)
% 0.45/0.69          | ~ (v3_orders_2 @ X6)
% 0.45/0.69          | (v2_struct_0 @ X6)
% 0.45/0.69          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.45/0.69          | (r3_orders_2 @ X6 @ X5 @ X7)
% 0.45/0.69          | ~ (r1_orders_2 @ X6 @ X5 @ X7))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.45/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.45/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.45/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.45/0.69          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.45/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('51', plain, (![X22 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X22))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.45/0.69  thf('52', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.45/0.69  thf('53', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.45/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.45/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.45/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | ~ (m1_subset_1 @ 
% 0.45/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.45/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['46', '53'])).
% 0.45/0.69  thf('55', plain,
% 0.45/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69        sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('56', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.45/0.69  thf(t3_yellow_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.45/0.69               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.45/0.69                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k2_yellow_1 @ X29)))
% 0.45/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.45/0.69          | (r1_tarski @ X28 @ X30)
% 0.45/0.69          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ (k2_yellow_1 @ X29)))
% 0.45/0.69          | (v1_xboole_0 @ X29))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('60', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('61', plain,
% 0.45/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X28 @ X29)
% 0.45/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.45/0.69          | (r1_tarski @ X28 @ X30)
% 0.45/0.69          | ~ (m1_subset_1 @ X30 @ X29)
% 0.45/0.69          | (v1_xboole_0 @ X29))),
% 0.45/0.69      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | (v1_xboole_0 @ sk_A)
% 0.45/0.69        | ~ (m1_subset_1 @ 
% 0.45/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.45/0.69        | (r1_tarski @ sk_C @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['57', '61'])).
% 0.45/0.69  thf('63', plain,
% 0.45/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69        sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('64', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | (v1_xboole_0 @ sk_A)
% 0.45/0.69        | (r1_tarski @ sk_C @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.45/0.69  thf(fc6_yellow_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.69       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.45/0.69         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.45/0.69  thf('66', plain,
% 0.45/0.69      (![X25 : $i]:
% 0.45/0.69         (~ (v2_struct_0 @ (k2_yellow_1 @ X25)) | (v1_xboole_0 @ X25))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69        | (v1_xboole_0 @ sk_A))),
% 0.45/0.69      inference('clc', [status(thm)], ['65', '66'])).
% 0.45/0.69  thf('68', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      ((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('clc', [status(thm)], ['67', '68'])).
% 0.45/0.69  thf('70', plain,
% 0.45/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.45/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['3', '16'])).
% 0.45/0.69  thf('71', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ((X16) != (k13_lattice3 @ X15 @ X14 @ X17))
% 0.45/0.69          | (r1_orders_2 @ X15 @ X14 @ X16)
% 0.45/0.69          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (l1_orders_2 @ X15)
% 0.45/0.69          | ~ (v1_lattice3 @ X15)
% 0.45/0.69          | ~ (v5_orders_2 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t22_yellow_0])).
% 0.45/0.69  thf('72', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.45/0.69         (~ (v5_orders_2 @ X15)
% 0.45/0.69          | ~ (v1_lattice3 @ X15)
% 0.45/0.69          | ~ (l1_orders_2 @ X15)
% 0.45/0.69          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.45/0.69          | (r1_orders_2 @ X15 @ X14 @ (k13_lattice3 @ X15 @ X14 @ X17))
% 0.45/0.69          | ~ (m1_subset_1 @ (k13_lattice3 @ X15 @ X14 @ X17) @ 
% 0.45/0.69               (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.69  thf('73', plain,
% 0.45/0.69      ((~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.45/0.69        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.45/0.69        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.45/0.69           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.45/0.69        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['70', '72'])).
% 0.45/0.69  thf('74', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('75', plain,
% 0.45/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69        sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('76', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('77', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf('78', plain,
% 0.45/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.45/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['3', '16'])).
% 0.45/0.69  thf('79', plain,
% 0.45/0.69      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.45/0.69  thf('80', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('81', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.45/0.69  thf('82', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('83', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.45/0.69  thf('84', plain,
% 0.45/0.69      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.45/0.69        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)],
% 0.45/0.69                ['73', '74', '75', '76', '77', '78', '79', '80', '81', '82', 
% 0.45/0.69                 '83'])).
% 0.45/0.69  thf('85', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.45/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.45/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.45/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.45/0.69  thf('86', plain,
% 0.45/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | ~ (m1_subset_1 @ 
% 0.45/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.45/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.69  thf('87', plain,
% 0.45/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69        sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('88', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf('89', plain,
% 0.45/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.45/0.69  thf('90', plain,
% 0.45/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X28 @ X29)
% 0.45/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.45/0.69          | (r1_tarski @ X28 @ X30)
% 0.45/0.69          | ~ (m1_subset_1 @ X30 @ X29)
% 0.45/0.69          | (v1_xboole_0 @ X29))),
% 0.45/0.69      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.45/0.69  thf('91', plain,
% 0.45/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | (v1_xboole_0 @ sk_A)
% 0.45/0.69        | ~ (m1_subset_1 @ 
% 0.45/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.45/0.69        | (r1_tarski @ sk_B @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['89', '90'])).
% 0.45/0.69  thf('92', plain,
% 0.45/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.69        sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('93', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf('94', plain,
% 0.45/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.45/0.69        | (v1_xboole_0 @ sk_A)
% 0.45/0.69        | (r1_tarski @ sk_B @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.45/0.69  thf('95', plain,
% 0.45/0.69      (![X25 : $i]:
% 0.45/0.69         (~ (v2_struct_0 @ (k2_yellow_1 @ X25)) | (v1_xboole_0 @ X25))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.45/0.69  thf('96', plain,
% 0.45/0.69      (((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69        | (v1_xboole_0 @ sk_A))),
% 0.45/0.69      inference('clc', [status(thm)], ['94', '95'])).
% 0.45/0.69  thf('97', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('98', plain,
% 0.45/0.69      ((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('clc', [status(thm)], ['96', '97'])).
% 0.45/0.69  thf(t8_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.45/0.69       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.45/0.69  thf('99', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (r1_tarski @ X0 @ X1)
% 0.45/0.69          | ~ (r1_tarski @ X2 @ X1)
% 0.45/0.69          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.45/0.69  thf('100', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 0.45/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.45/0.69          | ~ (r1_tarski @ X0 @ 
% 0.45/0.69               (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['98', '99'])).
% 0.45/0.69  thf('101', plain,
% 0.45/0.69      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.45/0.69        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['69', '100'])).
% 0.45/0.69  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
