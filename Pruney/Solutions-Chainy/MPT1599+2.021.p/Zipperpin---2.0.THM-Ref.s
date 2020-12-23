%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jBpF6wTmMm

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:08 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 672 expanded)
%              Number of leaves         :   33 ( 240 expanded)
%              Depth                    :   17
%              Number of atoms          : 1266 (8187 expanded)
%              Number of equality atoms :   33 ( 350 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( ( k12_lattice3 @ X12 @ X11 @ X13 )
        = ( k11_lattice3 @ X12 @ X11 @ X13 ) ) ) ),
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

thf(t23_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k12_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ D @ B )
                      & ( r1_orders_2 @ A @ D @ C )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ E @ B )
                              & ( r1_orders_2 @ A @ E @ C ) )
                           => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( X16
       != ( k12_lattice3 @ X15 @ X14 @ X17 ) )
      | ( r1_orders_2 @ X15 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v2_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow_0])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v5_orders_2 @ X15 )
      | ~ ( v2_lattice3 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ ( k12_lattice3 @ X15 @ X14 @ X17 ) @ X17 )
      | ~ ( m1_subset_1 @ ( k12_lattice3 @ X15 @ X14 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
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
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k12_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v2_lattice3 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k12_lattice3 @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k12_lattice3])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
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
      | ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('37',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
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
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
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
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X24: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('46',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
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
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('56',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('57',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
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
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('64',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
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
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( X16
       != ( k12_lattice3 @ X15 @ X14 @ X17 ) )
      | ( r1_orders_2 @ X15 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v2_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow_0])).

thf('72',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v5_orders_2 @ X15 )
      | ~ ( v2_lattice3 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ ( k12_lattice3 @ X15 @ X14 @ X17 ) @ X14 )
      | ~ ( m1_subset_1 @ ( k12_lattice3 @ X15 @ X14 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('75',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
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
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
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
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X24: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('84',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
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
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('88',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('89',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
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
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('93',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('94',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X25: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X25 ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('96',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['96','97'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['69','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jBpF6wTmMm
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.64  % Solved by: fo/fo7.sh
% 0.44/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.64  % done 242 iterations in 0.175s
% 0.44/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.64  % SZS output start Refutation
% 0.44/0.64  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.44/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.64  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.44/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.64  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.44/0.64  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.44/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.64  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.44/0.64  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.44/0.64  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.44/0.64  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.44/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.64  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.44/0.64  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.44/0.64  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.44/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.64  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.44/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.64  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.44/0.64  thf(t7_yellow_1, conjecture,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.64       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.44/0.64         ( ![B:$i]:
% 0.44/0.64           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.44/0.64             ( ![C:$i]:
% 0.44/0.64               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.44/0.64                 ( r1_tarski @
% 0.44/0.64                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.44/0.64                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.64    (~( ![A:$i]:
% 0.44/0.64        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.64          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.44/0.64            ( ![B:$i]:
% 0.44/0.64              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.44/0.64                ( ![C:$i]:
% 0.44/0.64                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.44/0.64                    ( r1_tarski @
% 0.44/0.64                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.44/0.64                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.44/0.64    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 0.44/0.64  thf('0', plain,
% 0.44/0.64      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('1', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(t1_yellow_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.44/0.64       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.44/0.64  thf('2', plain, (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.44/0.64  thf('4', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('5', plain, (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('6', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.64  thf('7', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('8', plain, (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf(redefinition_k12_lattice3, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.44/0.64         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.44/0.64         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.64       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.44/0.64  thf('9', plain,
% 0.44/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.44/0.64          | ~ (l1_orders_2 @ X12)
% 0.44/0.64          | ~ (v2_lattice3 @ X12)
% 0.44/0.64          | ~ (v5_orders_2 @ X12)
% 0.44/0.64          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.44/0.64          | ((k12_lattice3 @ X12 @ X11 @ X13)
% 0.44/0.64              = (k11_lattice3 @ X12 @ X11 @ X13)))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.44/0.64  thf('10', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.44/0.64          | ((k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.44/0.64              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.44/0.64          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.44/0.64          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.44/0.64          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.64  thf('11', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf(fc5_yellow_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.44/0.64       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.44/0.64       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.44/0.64       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.44/0.64  thf('12', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.44/0.64  thf(dt_k2_yellow_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.44/0.64       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.44/0.64  thf('13', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.44/0.64  thf('14', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.44/0.64          | ((k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.44/0.64              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ X0)
% 0.44/0.64          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.44/0.64      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.44/0.64  thf('15', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.44/0.64          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.44/0.64              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 0.44/0.64          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['7', '14'])).
% 0.44/0.64  thf('16', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.44/0.64          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 0.44/0.64              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['6', '15'])).
% 0.44/0.64  thf('17', plain,
% 0.44/0.64      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.44/0.64         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '16'])).
% 0.44/0.64  thf(t23_yellow_0, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.64           ( ![C:$i]:
% 0.44/0.64             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.64               ( ![D:$i]:
% 0.44/0.64                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.64                   ( ( ( D ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.44/0.64                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.44/0.64                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.44/0.64                       ( ![E:$i]:
% 0.44/0.64                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.64                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.44/0.64                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.44/0.64                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.64  thf('18', plain,
% 0.44/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.44/0.64          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.44/0.64          | ((X16) != (k12_lattice3 @ X15 @ X14 @ X17))
% 0.44/0.64          | (r1_orders_2 @ X15 @ X16 @ X17)
% 0.44/0.64          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.44/0.64          | ~ (l1_orders_2 @ X15)
% 0.44/0.64          | ~ (v2_lattice3 @ X15)
% 0.44/0.64          | ~ (v5_orders_2 @ X15))),
% 0.44/0.64      inference('cnf', [status(esa)], [t23_yellow_0])).
% 0.44/0.64  thf('19', plain,
% 0.44/0.64      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.44/0.64         (~ (v5_orders_2 @ X15)
% 0.44/0.64          | ~ (v2_lattice3 @ X15)
% 0.44/0.64          | ~ (l1_orders_2 @ X15)
% 0.44/0.64          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.44/0.64          | (r1_orders_2 @ X15 @ (k12_lattice3 @ X15 @ X14 @ X17) @ X17)
% 0.44/0.64          | ~ (m1_subset_1 @ (k12_lattice3 @ X15 @ X14 @ X17) @ 
% 0.44/0.64               (u1_struct_0 @ X15))
% 0.44/0.64          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['18'])).
% 0.44/0.64  thf('20', plain,
% 0.44/0.64      ((~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.44/0.64        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.44/0.64        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.44/0.64           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.44/0.64        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['17', '19'])).
% 0.44/0.64  thf('21', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('22', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.44/0.64  thf('23', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.64  thf('24', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('25', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf(dt_k12_lattice3, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.44/0.64         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.44/0.64         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.64       ( m1_subset_1 @ ( k12_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.44/0.64  thf('26', plain,
% 0.44/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.44/0.64          | ~ (l1_orders_2 @ X9)
% 0.44/0.64          | ~ (v2_lattice3 @ X9)
% 0.44/0.64          | ~ (v5_orders_2 @ X9)
% 0.44/0.64          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.44/0.64          | (m1_subset_1 @ (k12_lattice3 @ X9 @ X8 @ X10) @ (u1_struct_0 @ X9)))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k12_lattice3])).
% 0.44/0.64  thf('27', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.44/0.64          | (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.44/0.64             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.44/0.64          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.44/0.64          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.44/0.64          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.64  thf('28', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('29', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('30', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.44/0.64  thf('31', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.44/0.64  thf('32', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.44/0.64          | (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ X0)
% 0.44/0.64          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.44/0.64      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.44/0.64  thf('33', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.44/0.64          | (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0) @ 
% 0.44/0.64             sk_A)
% 0.44/0.64          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['24', '32'])).
% 0.44/0.64  thf('34', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.44/0.64          | (m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C) @ 
% 0.44/0.64             sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['23', '33'])).
% 0.44/0.64  thf('35', plain,
% 0.44/0.64      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64        sk_A)),
% 0.44/0.64      inference('sup-', [status(thm)], ['22', '34'])).
% 0.44/0.64  thf('36', plain,
% 0.44/0.64      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.44/0.64         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '16'])).
% 0.44/0.64  thf('37', plain,
% 0.44/0.64      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64        sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.64  thf('38', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('39', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.44/0.64  thf('40', plain,
% 0.44/0.64      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.44/0.64         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '16'])).
% 0.44/0.64  thf('41', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('42', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.64  thf('43', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.44/0.64  thf('44', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('45', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.44/0.64  thf('46', plain,
% 0.44/0.64      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.44/0.64        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.44/0.64      inference('demod', [status(thm)],
% 0.44/0.64                ['20', '21', '37', '38', '39', '40', '41', '42', '43', '44', 
% 0.44/0.64                 '45'])).
% 0.44/0.64  thf('47', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf(redefinition_r3_orders_2, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.64         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.44/0.64         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.64       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.44/0.64  thf('48', plain,
% 0.44/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.44/0.64          | ~ (l1_orders_2 @ X6)
% 0.44/0.64          | ~ (v3_orders_2 @ X6)
% 0.44/0.64          | (v2_struct_0 @ X6)
% 0.44/0.64          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.44/0.64          | (r3_orders_2 @ X6 @ X5 @ X7)
% 0.44/0.64          | ~ (r1_orders_2 @ X6 @ X5 @ X7))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.44/0.64  thf('49', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.44/0.64          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.44/0.64          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.44/0.64          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.44/0.64          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.44/0.64          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.64  thf('50', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('51', plain, (![X22 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X22))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.44/0.64  thf('52', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.44/0.64  thf('53', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.44/0.64          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.44/0.64          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ X0)
% 0.44/0.64          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.44/0.64      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.44/0.64  thf('54', plain,
% 0.44/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.44/0.64        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.44/0.64           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.44/0.64        | ~ (m1_subset_1 @ 
% 0.44/0.64             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['46', '53'])).
% 0.44/0.64  thf('55', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.64  thf('56', plain,
% 0.44/0.64      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64        sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.64  thf('57', plain,
% 0.44/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.44/0.64           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.44/0.64      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.44/0.64  thf(t3_yellow_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.44/0.64           ( ![C:$i]:
% 0.44/0.64             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.44/0.64               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.44/0.64                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.44/0.64  thf('58', plain,
% 0.44/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k2_yellow_1 @ X29)))
% 0.44/0.64          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.44/0.64          | (r1_tarski @ X28 @ X30)
% 0.44/0.64          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ (k2_yellow_1 @ X29)))
% 0.44/0.64          | (v1_xboole_0 @ X29))),
% 0.44/0.64      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.44/0.64  thf('59', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('60', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('61', plain,
% 0.44/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X28 @ X29)
% 0.44/0.64          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.44/0.64          | (r1_tarski @ X28 @ X30)
% 0.44/0.64          | ~ (m1_subset_1 @ X30 @ X29)
% 0.44/0.64          | (v1_xboole_0 @ X29))),
% 0.44/0.64      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.64  thf('62', plain,
% 0.44/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.44/0.64        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64           sk_C)
% 0.44/0.64        | ~ (m1_subset_1 @ 
% 0.44/0.64             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['57', '61'])).
% 0.44/0.64  thf('63', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.64  thf('64', plain,
% 0.44/0.64      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64        sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.64  thf('65', plain,
% 0.44/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64           sk_C))),
% 0.44/0.64      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.44/0.64  thf(fc6_yellow_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.64       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.44/0.64         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.44/0.64  thf('66', plain,
% 0.44/0.64      (![X25 : $i]:
% 0.44/0.64         (~ (v2_struct_0 @ (k2_yellow_1 @ X25)) | (v1_xboole_0 @ X25))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.44/0.64  thf('67', plain,
% 0.44/0.64      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.44/0.64        | (v1_xboole_0 @ sk_A))),
% 0.44/0.64      inference('clc', [status(thm)], ['65', '66'])).
% 0.44/0.64  thf('68', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('69', plain,
% 0.44/0.64      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.44/0.64      inference('clc', [status(thm)], ['67', '68'])).
% 0.44/0.64  thf('70', plain,
% 0.44/0.64      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.44/0.64         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '16'])).
% 0.44/0.64  thf('71', plain,
% 0.44/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.44/0.64          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.44/0.64          | ((X16) != (k12_lattice3 @ X15 @ X14 @ X17))
% 0.44/0.64          | (r1_orders_2 @ X15 @ X16 @ X14)
% 0.44/0.64          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.44/0.64          | ~ (l1_orders_2 @ X15)
% 0.44/0.64          | ~ (v2_lattice3 @ X15)
% 0.44/0.64          | ~ (v5_orders_2 @ X15))),
% 0.44/0.64      inference('cnf', [status(esa)], [t23_yellow_0])).
% 0.44/0.64  thf('72', plain,
% 0.44/0.64      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.44/0.64         (~ (v5_orders_2 @ X15)
% 0.44/0.64          | ~ (v2_lattice3 @ X15)
% 0.44/0.64          | ~ (l1_orders_2 @ X15)
% 0.44/0.64          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.44/0.64          | (r1_orders_2 @ X15 @ (k12_lattice3 @ X15 @ X14 @ X17) @ X14)
% 0.44/0.64          | ~ (m1_subset_1 @ (k12_lattice3 @ X15 @ X14 @ X17) @ 
% 0.44/0.64               (u1_struct_0 @ X15))
% 0.44/0.64          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['71'])).
% 0.44/0.64  thf('73', plain,
% 0.44/0.64      ((~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.44/0.64        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.44/0.64        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.44/0.64           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.44/0.64        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['70', '72'])).
% 0.44/0.64  thf('74', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('75', plain,
% 0.44/0.64      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64        sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.64  thf('76', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('77', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.44/0.64  thf('78', plain,
% 0.44/0.64      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.44/0.64         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '16'])).
% 0.44/0.64  thf('79', plain,
% 0.44/0.64      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.44/0.64  thf('80', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.44/0.64  thf('81', plain, (![X20 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X20))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.44/0.64  thf('82', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('83', plain, (![X24 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X24))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.44/0.64  thf('84', plain,
% 0.44/0.64      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.44/0.64        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.44/0.64      inference('demod', [status(thm)],
% 0.44/0.64                ['73', '74', '75', '76', '77', '78', '79', '80', '81', '82', 
% 0.44/0.64                 '83'])).
% 0.44/0.64  thf('85', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X1 @ X0)
% 0.44/0.64          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.44/0.64          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ X0)
% 0.44/0.64          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.44/0.64      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.44/0.64  thf('86', plain,
% 0.44/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.44/0.64        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.44/0.64           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.44/0.64        | ~ (m1_subset_1 @ 
% 0.44/0.64             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['84', '85'])).
% 0.44/0.64  thf('87', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.44/0.64  thf('88', plain,
% 0.44/0.64      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64        sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.64  thf('89', plain,
% 0.44/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.44/0.64           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.44/0.64  thf('90', plain,
% 0.44/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X28 @ X29)
% 0.44/0.64          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.44/0.64          | (r1_tarski @ X28 @ X30)
% 0.44/0.64          | ~ (m1_subset_1 @ X30 @ X29)
% 0.44/0.64          | (v1_xboole_0 @ X29))),
% 0.44/0.64      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.64  thf('91', plain,
% 0.44/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.44/0.64        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64           sk_B)
% 0.44/0.64        | ~ (m1_subset_1 @ 
% 0.44/0.64             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.44/0.64  thf('92', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.44/0.64  thf('93', plain,
% 0.44/0.64      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64        sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.64  thf('94', plain,
% 0.44/0.64      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64           sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.44/0.64  thf('95', plain,
% 0.44/0.64      (![X25 : $i]:
% 0.44/0.64         (~ (v2_struct_0 @ (k2_yellow_1 @ X25)) | (v1_xboole_0 @ X25))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.44/0.64  thf('96', plain,
% 0.44/0.64      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_A))),
% 0.44/0.64      inference('clc', [status(thm)], ['94', '95'])).
% 0.44/0.64  thf('97', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('98', plain,
% 0.44/0.64      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.44/0.64      inference('clc', [status(thm)], ['96', '97'])).
% 0.44/0.64  thf(t19_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.44/0.64       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.64  thf('99', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.44/0.64          | ~ (r1_tarski @ X0 @ X2)
% 0.44/0.64          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.44/0.64  thf('100', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64           (k3_xboole_0 @ sk_B @ X0))
% 0.44/0.64          | ~ (r1_tarski @ 
% 0.44/0.64               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['98', '99'])).
% 0.44/0.64  thf('101', plain,
% 0.44/0.64      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.44/0.64        (k3_xboole_0 @ sk_B @ sk_C))),
% 0.44/0.64      inference('sup-', [status(thm)], ['69', '100'])).
% 0.44/0.64  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 0.44/0.64  
% 0.44/0.64  % SZS output end Refutation
% 0.44/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
