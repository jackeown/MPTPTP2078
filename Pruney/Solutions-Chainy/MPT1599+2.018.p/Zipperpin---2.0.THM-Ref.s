%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.raExDaWfpl

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:08 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 519 expanded)
%              Number of leaves         :   33 ( 190 expanded)
%              Depth                    :   18
%              Number of atoms          : 1326 (6279 expanded)
%              Number of equality atoms :   33 ( 255 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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
    ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
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
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( ( k12_lattice3 @ X17 @ X16 @ X18 )
        = ( k11_lattice3 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X27: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

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

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k11_lattice3 @ X12 @ X11 @ X14 ) )
      | ( r1_orders_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ ( k11_lattice3 @ X12 @ X11 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X12 @ X11 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('26',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k12_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v2_lattice3 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k12_lattice3 @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k12_lattice3])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('31',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('32',plain,(
    ! [X27: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('33',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('40',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('41',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('43',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('44',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X27: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('46',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','37','38','39','40','41','42','43','44','45'])).

thf('47',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
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
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('51',plain,(
    ! [X25: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('52',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
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
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('56',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('57',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('59',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X32 ) @ X31 @ X33 )
      | ( r1_tarski @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X32 ) @ X31 @ X33 )
      | ( r1_tarski @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('65',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('66',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X28: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X28 ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('68',plain,
    ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k11_lattice3 @ X12 @ X11 @ X14 ) )
      | ( r1_orders_2 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('73',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ ( k11_lattice3 @ X12 @ X11 @ X14 ) @ X11 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X12 @ X11 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('76',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('77',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('79',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('80',plain,(
    ! [X29: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('82',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('83',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X27: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('85',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79','80','81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('87',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('89',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('90',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X32 ) @ X31 @ X33 )
      | ( r1_tarski @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('93',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('95',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('96',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X28: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X28 ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('98',plain,
    ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['98','99'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['70','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['18','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.raExDaWfpl
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.86  % Solved by: fo/fo7.sh
% 0.69/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.86  % done 318 iterations in 0.411s
% 0.69/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.86  % SZS output start Refutation
% 0.69/0.86  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.69/0.86  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.69/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.86  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.69/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.86  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.69/0.86  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.69/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.86  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.69/0.86  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.69/0.86  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.69/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.69/0.86  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.69/0.86  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.69/0.86  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.69/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.86  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.69/0.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.86  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.69/0.86  thf(t7_yellow_1, conjecture,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.86       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.69/0.86         ( ![B:$i]:
% 0.69/0.86           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.86             ( ![C:$i]:
% 0.69/0.86               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.86                 ( r1_tarski @
% 0.69/0.86                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.69/0.86                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.86    (~( ![A:$i]:
% 0.69/0.86        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.86          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.69/0.86            ( ![B:$i]:
% 0.69/0.86              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.86                ( ![C:$i]:
% 0.69/0.86                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.86                    ( r1_tarski @
% 0.69/0.86                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.69/0.86                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.69/0.86    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 0.69/0.86  thf('0', plain,
% 0.69/0.86      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('1', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(t1_yellow_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.69/0.86       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.69/0.86  thf('2', plain, (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.86  thf('4', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('5', plain, (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('6', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.86  thf('7', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('8', plain, (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf(redefinition_k12_lattice3, axiom,
% 0.69/0.86    (![A:$i,B:$i,C:$i]:
% 0.69/0.86     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.69/0.86         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.69/0.86         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.69/0.86  thf('9', plain,
% 0.69/0.86      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.69/0.86          | ~ (l1_orders_2 @ X17)
% 0.69/0.86          | ~ (v2_lattice3 @ X17)
% 0.69/0.86          | ~ (v5_orders_2 @ X17)
% 0.69/0.86          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.69/0.86          | ((k12_lattice3 @ X17 @ X16 @ X18)
% 0.69/0.86              = (k11_lattice3 @ X17 @ X16 @ X18)))),
% 0.69/0.86      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.69/0.86  thf('10', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ X0)
% 0.69/0.86          | ((k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.69/0.86              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.69/0.86          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.69/0.86          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.69/0.86          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.86  thf('11', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf(fc5_yellow_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.69/0.86       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.69/0.86       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.69/0.86       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.69/0.86  thf('12', plain, (![X27 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X27))),
% 0.69/0.86      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.86  thf(dt_k2_yellow_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.69/0.86       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.69/0.86  thf('13', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.86  thf('14', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ X0)
% 0.69/0.86          | ((k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.69/0.86              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ X0)
% 0.69/0.86          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.69/0.86      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.69/0.86  thf('15', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.86          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.69/0.86              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 0.69/0.86          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['7', '14'])).
% 0.69/0.86  thf('16', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.86          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 0.69/0.86              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['6', '15'])).
% 0.69/0.86  thf('17', plain,
% 0.69/0.86      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.86         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['3', '16'])).
% 0.69/0.86  thf('18', plain,
% 0.69/0.86      (~ (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['0', '17'])).
% 0.69/0.86  thf('19', plain,
% 0.69/0.86      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.86         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['3', '16'])).
% 0.69/0.86  thf(l28_lattice3, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.69/0.86         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.86           ( ![C:$i]:
% 0.69/0.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.86               ( ![D:$i]:
% 0.69/0.86                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.86                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 0.69/0.86                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.69/0.86                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.69/0.86                       ( ![E:$i]:
% 0.69/0.86                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.86                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.69/0.86                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.69/0.86                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf('20', plain,
% 0.69/0.86      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.69/0.86          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.69/0.86          | ((X13) != (k11_lattice3 @ X12 @ X11 @ X14))
% 0.69/0.86          | (r1_orders_2 @ X12 @ X13 @ X14)
% 0.69/0.86          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.69/0.86          | ~ (l1_orders_2 @ X12)
% 0.69/0.86          | ~ (v2_lattice3 @ X12)
% 0.69/0.86          | ~ (v5_orders_2 @ X12)
% 0.69/0.86          | (v2_struct_0 @ X12))),
% 0.69/0.86      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.69/0.86  thf('21', plain,
% 0.69/0.86      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X12)
% 0.69/0.86          | ~ (v5_orders_2 @ X12)
% 0.69/0.86          | ~ (v2_lattice3 @ X12)
% 0.69/0.86          | ~ (l1_orders_2 @ X12)
% 0.69/0.86          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.69/0.86          | (r1_orders_2 @ X12 @ (k11_lattice3 @ X12 @ X11 @ X14) @ X14)
% 0.69/0.86          | ~ (m1_subset_1 @ (k11_lattice3 @ X12 @ X11 @ X14) @ 
% 0.69/0.86               (u1_struct_0 @ X12))
% 0.69/0.86          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['20'])).
% 0.69/0.86  thf('22', plain,
% 0.69/0.86      ((~ (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.86        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.86        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.69/0.86        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.86        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['19', '21'])).
% 0.69/0.86  thf('23', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('24', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.86  thf('25', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.86  thf('26', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('27', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf(dt_k12_lattice3, axiom,
% 0.69/0.86    (![A:$i,B:$i,C:$i]:
% 0.69/0.86     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.69/0.86         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.69/0.86         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86       ( m1_subset_1 @ ( k12_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.69/0.86  thf('28', plain,
% 0.69/0.86      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.69/0.86          | ~ (l1_orders_2 @ X9)
% 0.69/0.86          | ~ (v2_lattice3 @ X9)
% 0.69/0.86          | ~ (v5_orders_2 @ X9)
% 0.69/0.86          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.69/0.86          | (m1_subset_1 @ (k12_lattice3 @ X9 @ X8 @ X10) @ (u1_struct_0 @ X9)))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k12_lattice3])).
% 0.69/0.86  thf('29', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ X0)
% 0.69/0.86          | (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.69/0.86             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.69/0.86          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.69/0.86          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.69/0.86          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.86  thf('30', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('31', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('32', plain, (![X27 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X27))),
% 0.69/0.86      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.86  thf('33', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.86  thf('34', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ X0)
% 0.69/0.86          | (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ X0)
% 0.69/0.86          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.69/0.86      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.69/0.86  thf('35', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.86          | (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0) @ 
% 0.69/0.86             sk_A)
% 0.69/0.86          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['26', '34'])).
% 0.69/0.86  thf('36', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.86          | (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C) @ 
% 0.69/0.86             sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['25', '35'])).
% 0.69/0.86  thf('37', plain,
% 0.69/0.86      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86        sk_A)),
% 0.69/0.86      inference('sup-', [status(thm)], ['24', '36'])).
% 0.69/0.86  thf('38', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('39', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.86  thf('40', plain,
% 0.69/0.86      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.86         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['3', '16'])).
% 0.69/0.86  thf('41', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('42', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.86  thf('43', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.86  thf('44', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('45', plain, (![X27 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X27))),
% 0.69/0.86      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.86  thf('46', plain,
% 0.69/0.86      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.86      inference('demod', [status(thm)],
% 0.69/0.86                ['22', '23', '37', '38', '39', '40', '41', '42', '43', '44', 
% 0.69/0.86                 '45'])).
% 0.69/0.86  thf('47', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf(redefinition_r3_orders_2, axiom,
% 0.69/0.86    (![A:$i,B:$i,C:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.69/0.86         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.69/0.86         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.69/0.86  thf('48', plain,
% 0.69/0.86      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.69/0.86          | ~ (l1_orders_2 @ X6)
% 0.69/0.86          | ~ (v3_orders_2 @ X6)
% 0.69/0.86          | (v2_struct_0 @ X6)
% 0.69/0.86          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.69/0.86          | (r3_orders_2 @ X6 @ X5 @ X7)
% 0.69/0.86          | ~ (r1_orders_2 @ X6 @ X5 @ X7))),
% 0.69/0.86      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.69/0.86  thf('49', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ X0)
% 0.69/0.86          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.69/0.86          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.69/0.86          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.69/0.86          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.69/0.86          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['47', '48'])).
% 0.69/0.86  thf('50', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('51', plain, (![X25 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X25))),
% 0.69/0.86      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.86  thf('52', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.86  thf('53', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ X0)
% 0.69/0.86          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.69/0.86          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ X0)
% 0.69/0.86          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.69/0.86      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.69/0.86  thf('54', plain,
% 0.69/0.86      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.69/0.86        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.69/0.86        | ~ (m1_subset_1 @ 
% 0.69/0.86             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['46', '53'])).
% 0.69/0.86  thf('55', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.86  thf('56', plain,
% 0.69/0.86      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86        sk_A)),
% 0.69/0.86      inference('sup-', [status(thm)], ['24', '36'])).
% 0.69/0.86  thf('57', plain,
% 0.69/0.86      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.69/0.86  thf('58', plain,
% 0.69/0.86      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['57'])).
% 0.69/0.86  thf(t3_yellow_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.86           ( ![C:$i]:
% 0.69/0.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.86               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.69/0.86                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.69/0.86  thf('59', plain,
% 0.69/0.86      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ (k2_yellow_1 @ X32)))
% 0.69/0.86          | ~ (r3_orders_2 @ (k2_yellow_1 @ X32) @ X31 @ X33)
% 0.69/0.86          | (r1_tarski @ X31 @ X33)
% 0.69/0.86          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ (k2_yellow_1 @ X32)))
% 0.69/0.86          | (v1_xboole_0 @ X32))),
% 0.69/0.86      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.69/0.86  thf('60', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('61', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('62', plain,
% 0.69/0.86      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X31 @ X32)
% 0.69/0.86          | ~ (r3_orders_2 @ (k2_yellow_1 @ X32) @ X31 @ X33)
% 0.69/0.86          | (r1_tarski @ X31 @ X33)
% 0.69/0.86          | ~ (m1_subset_1 @ X33 @ X32)
% 0.69/0.86          | (v1_xboole_0 @ X32))),
% 0.69/0.86      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.69/0.86  thf('63', plain,
% 0.69/0.86      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v1_xboole_0 @ sk_A)
% 0.69/0.86        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.69/0.86        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86           sk_C)
% 0.69/0.86        | ~ (m1_subset_1 @ 
% 0.69/0.86             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['58', '62'])).
% 0.69/0.86  thf('64', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.86  thf('65', plain,
% 0.69/0.86      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86        sk_A)),
% 0.69/0.86      inference('sup-', [status(thm)], ['24', '36'])).
% 0.69/0.86  thf('66', plain,
% 0.69/0.86      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v1_xboole_0 @ sk_A)
% 0.69/0.86        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86           sk_C))),
% 0.69/0.86      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.69/0.86  thf(fc6_yellow_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.86       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.69/0.86         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.69/0.86  thf('67', plain,
% 0.69/0.86      (![X28 : $i]:
% 0.69/0.86         (~ (v2_struct_0 @ (k2_yellow_1 @ X28)) | (v1_xboole_0 @ X28))),
% 0.69/0.86      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.69/0.86  thf('68', plain,
% 0.69/0.86      (((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.69/0.86        | (v1_xboole_0 @ sk_A))),
% 0.69/0.86      inference('clc', [status(thm)], ['66', '67'])).
% 0.69/0.86  thf('69', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('70', plain,
% 0.69/0.86      ((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.69/0.86      inference('clc', [status(thm)], ['68', '69'])).
% 0.69/0.86  thf('71', plain,
% 0.69/0.86      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.86         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['3', '16'])).
% 0.69/0.86  thf('72', plain,
% 0.69/0.86      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.69/0.86          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.69/0.86          | ((X13) != (k11_lattice3 @ X12 @ X11 @ X14))
% 0.69/0.86          | (r1_orders_2 @ X12 @ X13 @ X11)
% 0.69/0.86          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.69/0.86          | ~ (l1_orders_2 @ X12)
% 0.69/0.86          | ~ (v2_lattice3 @ X12)
% 0.69/0.86          | ~ (v5_orders_2 @ X12)
% 0.69/0.86          | (v2_struct_0 @ X12))),
% 0.69/0.86      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.69/0.86  thf('73', plain,
% 0.69/0.86      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X12)
% 0.69/0.86          | ~ (v5_orders_2 @ X12)
% 0.69/0.86          | ~ (v2_lattice3 @ X12)
% 0.69/0.86          | ~ (l1_orders_2 @ X12)
% 0.69/0.86          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.69/0.86          | (r1_orders_2 @ X12 @ (k11_lattice3 @ X12 @ X11 @ X14) @ X11)
% 0.69/0.86          | ~ (m1_subset_1 @ (k11_lattice3 @ X12 @ X11 @ X14) @ 
% 0.69/0.86               (u1_struct_0 @ X12))
% 0.69/0.86          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['72'])).
% 0.69/0.86  thf('74', plain,
% 0.69/0.86      ((~ (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.86        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.86        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.69/0.86        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.86        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['71', '73'])).
% 0.69/0.86  thf('75', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('76', plain,
% 0.69/0.86      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86        sk_A)),
% 0.69/0.86      inference('sup-', [status(thm)], ['24', '36'])).
% 0.69/0.86  thf('77', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('78', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.86  thf('79', plain,
% 0.69/0.86      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.86         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['3', '16'])).
% 0.69/0.86  thf('80', plain,
% 0.69/0.86      (![X29 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X29)) = (X29))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.69/0.86  thf('81', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.86  thf('82', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.86  thf('83', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('84', plain, (![X27 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X27))),
% 0.69/0.86      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.86  thf('85', plain,
% 0.69/0.86      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.86      inference('demod', [status(thm)],
% 0.69/0.86                ['74', '75', '76', '77', '78', '79', '80', '81', '82', '83', 
% 0.69/0.86                 '84'])).
% 0.69/0.86  thf('86', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ X0)
% 0.69/0.86          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.69/0.86          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ X0)
% 0.69/0.86          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.69/0.86      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.69/0.86  thf('87', plain,
% 0.69/0.86      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.69/0.86        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.69/0.86        | ~ (m1_subset_1 @ 
% 0.69/0.86             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['85', '86'])).
% 0.69/0.86  thf('88', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.86  thf('89', plain,
% 0.69/0.86      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86        sk_A)),
% 0.69/0.86      inference('sup-', [status(thm)], ['24', '36'])).
% 0.69/0.86  thf('90', plain,
% 0.69/0.86      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.69/0.86      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.69/0.86  thf('91', plain,
% 0.69/0.86      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.86         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.69/0.86        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['90'])).
% 0.69/0.86  thf('92', plain,
% 0.69/0.86      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X31 @ X32)
% 0.69/0.86          | ~ (r3_orders_2 @ (k2_yellow_1 @ X32) @ X31 @ X33)
% 0.69/0.86          | (r1_tarski @ X31 @ X33)
% 0.69/0.86          | ~ (m1_subset_1 @ X33 @ X32)
% 0.69/0.86          | (v1_xboole_0 @ X32))),
% 0.69/0.86      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.69/0.86  thf('93', plain,
% 0.69/0.86      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v1_xboole_0 @ sk_A)
% 0.69/0.86        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.69/0.86        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86           sk_B)
% 0.69/0.86        | ~ (m1_subset_1 @ 
% 0.69/0.86             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['91', '92'])).
% 0.69/0.86  thf('94', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.86  thf('95', plain,
% 0.69/0.86      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86        sk_A)),
% 0.69/0.86      inference('sup-', [status(thm)], ['24', '36'])).
% 0.69/0.86  thf('96', plain,
% 0.69/0.86      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.86        | (v1_xboole_0 @ sk_A)
% 0.69/0.86        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86           sk_B))),
% 0.69/0.86      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.69/0.86  thf('97', plain,
% 0.69/0.86      (![X28 : $i]:
% 0.69/0.86         (~ (v2_struct_0 @ (k2_yellow_1 @ X28)) | (v1_xboole_0 @ X28))),
% 0.69/0.86      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.69/0.86  thf('98', plain,
% 0.69/0.86      (((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.69/0.86        | (v1_xboole_0 @ sk_A))),
% 0.69/0.86      inference('clc', [status(thm)], ['96', '97'])).
% 0.69/0.86  thf('99', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('100', plain,
% 0.69/0.86      ((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.69/0.86      inference('clc', [status(thm)], ['98', '99'])).
% 0.69/0.86  thf(t19_xboole_1, axiom,
% 0.69/0.86    (![A:$i,B:$i,C:$i]:
% 0.69/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.69/0.86       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.69/0.86  thf('101', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (r1_tarski @ X0 @ X1)
% 0.69/0.86          | ~ (r1_tarski @ X0 @ X2)
% 0.69/0.86          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.69/0.86      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.69/0.86  thf('102', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86           (k3_xboole_0 @ sk_B @ X0))
% 0.69/0.86          | ~ (r1_tarski @ 
% 0.69/0.86               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['100', '101'])).
% 0.69/0.86  thf('103', plain,
% 0.69/0.86      ((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.86        (k3_xboole_0 @ sk_B @ sk_C))),
% 0.69/0.86      inference('sup-', [status(thm)], ['70', '102'])).
% 0.69/0.86  thf('104', plain, ($false), inference('demod', [status(thm)], ['18', '103'])).
% 0.69/0.86  
% 0.69/0.86  % SZS output end Refutation
% 0.69/0.86  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
