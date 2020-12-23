%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bD3nypEq7Q

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:04 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 519 expanded)
%              Number of leaves         :   33 ( 190 expanded)
%              Depth                    :   18
%              Number of atoms          : 1326 (6279 expanded)
%              Number of equality atoms :   33 ( 255 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

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
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k13_lattice3 @ X16 @ X15 @ X17 )
        = ( k10_lattice3 @ X16 @ X15 @ X17 ) ) ) ),
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
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
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

thf('18',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

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

thf('20',plain,(
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

thf('21',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ X13 @ ( k10_lattice3 @ X11 @ X10 @ X13 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X11 @ X10 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('26',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k13_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k13_lattice3 @ X8 @ X7 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k13_lattice3])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('31',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('32',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('33',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('40',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('41',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('43',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('44',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('46',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','37','38','39','40','41','42','43','44','45'])).

thf('47',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
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
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('51',plain,(
    ! [X24: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('52',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
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
    | ~ ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('57',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X31 ) @ X30 @ X32 )
      | ( r1_tarski @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) ) )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('60',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('61',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('62',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X31 ) @ X30 @ X32 )
      | ( r1_tarski @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('66',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X27: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X27 ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('68',plain,
    ( ( r1_tarski @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r1_tarski @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ X10 @ ( k10_lattice3 @ X11 @ X10 @ X13 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X11 @ X10 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('76',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('77',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('79',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('80',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('82',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('83',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('85',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
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
    | ~ ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('90',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X31 ) @ X30 @ X32 )
      | ( r1_tarski @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('93',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['24','36'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('96',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X27: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X27 ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('98',plain,
    ( ( r1_tarski @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r1_tarski @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['98','99'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['70','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['18','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bD3nypEq7Q
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:28:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.58/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.84  % Solved by: fo/fo7.sh
% 0.58/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.84  % done 318 iterations in 0.372s
% 0.58/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.84  % SZS output start Refutation
% 0.58/0.84  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.58/0.84  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.58/0.84  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.58/0.84  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.58/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.84  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.58/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.84  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.58/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.84  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.58/0.84  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.58/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.84  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.58/0.84  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.58/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.84  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.58/0.84  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.58/0.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.84  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.58/0.84  thf(t6_yellow_1, conjecture,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.84       ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.58/0.84         ( ![B:$i]:
% 0.58/0.84           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.58/0.84             ( ![C:$i]:
% 0.58/0.84               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.58/0.84                 ( r1_tarski @
% 0.58/0.84                   ( k2_xboole_0 @ B @ C ) @ 
% 0.58/0.84                   ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.58/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.84    (~( ![A:$i]:
% 0.58/0.84        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.84          ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.58/0.84            ( ![B:$i]:
% 0.58/0.84              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.58/0.84                ( ![C:$i]:
% 0.58/0.84                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.58/0.84                    ( r1_tarski @
% 0.58/0.84                      ( k2_xboole_0 @ B @ C ) @ 
% 0.58/0.84                      ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.58/0.84    inference('cnf.neg', [status(esa)], [t6_yellow_1])).
% 0.58/0.84  thf('0', plain,
% 0.58/0.84      (~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.58/0.84          (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('1', plain,
% 0.58/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf(t1_yellow_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.58/0.84       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.84  thf('2', plain, (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.84  thf('4', plain,
% 0.58/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('5', plain, (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('6', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.84  thf('7', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('8', plain, (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf(redefinition_k13_lattice3, axiom,
% 0.58/0.84    (![A:$i,B:$i,C:$i]:
% 0.58/0.84     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.58/0.84         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.58/0.84         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.84       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.58/0.84  thf('9', plain,
% 0.58/0.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.58/0.84          | ~ (l1_orders_2 @ X16)
% 0.58/0.84          | ~ (v1_lattice3 @ X16)
% 0.58/0.84          | ~ (v5_orders_2 @ X16)
% 0.58/0.84          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.58/0.84          | ((k13_lattice3 @ X16 @ X15 @ X17)
% 0.58/0.84              = (k10_lattice3 @ X16 @ X15 @ X17)))),
% 0.58/0.84      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.58/0.84  thf('10', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X1 @ X0)
% 0.58/0.84          | ((k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.58/0.84              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.58/0.84          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.58/0.84          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.58/0.84          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.58/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.84  thf('11', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf(fc5_yellow_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.58/0.84       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.58/0.84       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.58/0.84       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.58/0.84  thf('12', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.58/0.84  thf(dt_k2_yellow_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.58/0.84       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.58/0.84  thf('13', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.58/0.84  thf('14', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X1 @ X0)
% 0.58/0.84          | ((k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.58/0.84              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.58/0.84          | ~ (m1_subset_1 @ X2 @ X0)
% 0.58/0.84          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.58/0.84  thf('15', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.58/0.84          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.58/0.84              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 0.58/0.84          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['7', '14'])).
% 0.58/0.84  thf('16', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.58/0.84          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 0.58/0.84              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['6', '15'])).
% 0.58/0.84  thf('17', plain,
% 0.58/0.84      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.58/0.84         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('sup-', [status(thm)], ['3', '16'])).
% 0.58/0.84  thf('18', plain,
% 0.58/0.84      (~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.58/0.84          (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('demod', [status(thm)], ['0', '17'])).
% 0.58/0.84  thf('19', plain,
% 0.58/0.84      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.58/0.84         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('sup-', [status(thm)], ['3', '16'])).
% 0.58/0.84  thf(l26_lattice3, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.58/0.84         ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.84       ( ![B:$i]:
% 0.58/0.84         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.84           ( ![C:$i]:
% 0.58/0.84             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.84               ( ![D:$i]:
% 0.58/0.84                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.84                   ( ( ( D ) = ( k10_lattice3 @ A @ B @ C ) ) <=>
% 0.58/0.84                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.58/0.84                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.58/0.84                       ( ![E:$i]:
% 0.58/0.84                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.84                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.58/0.84                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.58/0.84                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.84  thf('20', plain,
% 0.58/0.84      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.58/0.84          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.58/0.84          | ((X12) != (k10_lattice3 @ X11 @ X10 @ X13))
% 0.58/0.84          | (r1_orders_2 @ X11 @ X13 @ X12)
% 0.58/0.84          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.58/0.84          | ~ (l1_orders_2 @ X11)
% 0.58/0.84          | ~ (v1_lattice3 @ X11)
% 0.58/0.84          | ~ (v5_orders_2 @ X11)
% 0.58/0.84          | (v2_struct_0 @ X11))),
% 0.58/0.84      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.58/0.84  thf('21', plain,
% 0.58/0.84      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.58/0.84         ((v2_struct_0 @ X11)
% 0.58/0.84          | ~ (v5_orders_2 @ X11)
% 0.58/0.84          | ~ (v1_lattice3 @ X11)
% 0.58/0.84          | ~ (l1_orders_2 @ X11)
% 0.58/0.84          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.58/0.84          | (r1_orders_2 @ X11 @ X13 @ (k10_lattice3 @ X11 @ X10 @ X13))
% 0.58/0.84          | ~ (m1_subset_1 @ (k10_lattice3 @ X11 @ X10 @ X13) @ 
% 0.58/0.84               (u1_struct_0 @ X11))
% 0.58/0.84          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11)))),
% 0.58/0.84      inference('simplify', [status(thm)], ['20'])).
% 0.58/0.84  thf('22', plain,
% 0.58/0.84      ((~ (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.58/0.84           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.58/0.84        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.58/0.84        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.58/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.58/0.84        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['19', '21'])).
% 0.58/0.84  thf('23', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('24', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.84  thf('25', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.84  thf('26', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('27', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf(dt_k13_lattice3, axiom,
% 0.58/0.84    (![A:$i,B:$i,C:$i]:
% 0.58/0.84     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.58/0.84         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.58/0.84         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.84       ( m1_subset_1 @ ( k13_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.58/0.84  thf('28', plain,
% 0.58/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.58/0.84          | ~ (l1_orders_2 @ X8)
% 0.58/0.84          | ~ (v1_lattice3 @ X8)
% 0.58/0.84          | ~ (v5_orders_2 @ X8)
% 0.58/0.84          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.58/0.84          | (m1_subset_1 @ (k13_lattice3 @ X8 @ X7 @ X9) @ (u1_struct_0 @ X8)))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k13_lattice3])).
% 0.58/0.84  thf('29', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X1 @ X0)
% 0.58/0.84          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.58/0.84             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.58/0.84          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.58/0.84          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.58/0.84          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.58/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.58/0.84  thf('30', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('31', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('32', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.58/0.84  thf('33', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.58/0.84  thf('34', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X1 @ X0)
% 0.58/0.84          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.58/0.84          | ~ (m1_subset_1 @ X2 @ X0)
% 0.58/0.84          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.58/0.84  thf('35', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.58/0.84          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0) @ 
% 0.58/0.84             sk_A)
% 0.58/0.84          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['26', '34'])).
% 0.58/0.84  thf('36', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.58/0.84          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C) @ 
% 0.58/0.84             sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['25', '35'])).
% 0.58/0.84  thf('37', plain,
% 0.58/0.84      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.58/0.84        sk_A)),
% 0.58/0.84      inference('sup-', [status(thm)], ['24', '36'])).
% 0.58/0.84  thf('38', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('39', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.84  thf('40', plain,
% 0.58/0.84      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.58/0.84         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('sup-', [status(thm)], ['3', '16'])).
% 0.58/0.84  thf('41', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('42', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.84  thf('43', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.58/0.84  thf('44', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('45', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.58/0.84  thf('46', plain,
% 0.58/0.84      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.58/0.84         (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.58/0.84      inference('demod', [status(thm)],
% 0.58/0.84                ['22', '23', '37', '38', '39', '40', '41', '42', '43', '44', 
% 0.58/0.84                 '45'])).
% 0.58/0.84  thf('47', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf(redefinition_r3_orders_2, axiom,
% 0.58/0.84    (![A:$i,B:$i,C:$i]:
% 0.58/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.84         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.58/0.84         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.84       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.58/0.84  thf('48', plain,
% 0.58/0.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.58/0.84          | ~ (l1_orders_2 @ X4)
% 0.58/0.84          | ~ (v3_orders_2 @ X4)
% 0.58/0.84          | (v2_struct_0 @ X4)
% 0.58/0.84          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.58/0.84          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.58/0.84          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.58/0.84      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.58/0.84  thf('49', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X1 @ X0)
% 0.58/0.84          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.58/0.84          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.58/0.84          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.58/0.84          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.58/0.84          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.58/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.84  thf('50', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('51', plain, (![X24 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X24))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.58/0.84  thf('52', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.58/0.84  thf('53', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X1 @ X0)
% 0.58/0.84          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.58/0.84          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.58/0.84          | ~ (m1_subset_1 @ X2 @ X0)
% 0.58/0.84          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.58/0.84  thf('54', plain,
% 0.58/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | ~ (m1_subset_1 @ 
% 0.58/0.84             (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.58/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['46', '53'])).
% 0.58/0.84  thf('55', plain,
% 0.58/0.84      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.58/0.84        sk_A)),
% 0.58/0.84      inference('sup-', [status(thm)], ['24', '36'])).
% 0.58/0.84  thf('56', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.84  thf('57', plain,
% 0.58/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.58/0.84      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.58/0.84  thf('58', plain,
% 0.58/0.84      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.58/0.84         (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.58/0.84      inference('simplify', [status(thm)], ['57'])).
% 0.58/0.84  thf(t3_yellow_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.84       ( ![B:$i]:
% 0.58/0.84         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.58/0.84           ( ![C:$i]:
% 0.58/0.84             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.58/0.84               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.58/0.84                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.58/0.84  thf('59', plain,
% 0.58/0.84      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ (k2_yellow_1 @ X31)))
% 0.58/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ X31) @ X30 @ X32)
% 0.58/0.84          | (r1_tarski @ X30 @ X32)
% 0.58/0.84          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ (k2_yellow_1 @ X31)))
% 0.58/0.84          | (v1_xboole_0 @ X31))),
% 0.58/0.84      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.58/0.84  thf('60', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('61', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('62', plain,
% 0.58/0.84      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X30 @ X31)
% 0.58/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ X31) @ X30 @ X32)
% 0.58/0.84          | (r1_tarski @ X30 @ X32)
% 0.58/0.84          | ~ (m1_subset_1 @ X32 @ X31)
% 0.58/0.84          | (v1_xboole_0 @ X31))),
% 0.58/0.84      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.58/0.84  thf('63', plain,
% 0.58/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v1_xboole_0 @ sk_A)
% 0.58/0.84        | ~ (m1_subset_1 @ 
% 0.58/0.84             (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.58/0.84        | (r1_tarski @ sk_C @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['58', '62'])).
% 0.58/0.84  thf('64', plain,
% 0.58/0.84      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.58/0.84        sk_A)),
% 0.58/0.84      inference('sup-', [status(thm)], ['24', '36'])).
% 0.58/0.84  thf('65', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.84  thf('66', plain,
% 0.58/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v1_xboole_0 @ sk_A)
% 0.58/0.84        | (r1_tarski @ sk_C @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.58/0.84      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.58/0.84  thf(fc6_yellow_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.84       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.58/0.84         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.58/0.84  thf('67', plain,
% 0.58/0.84      (![X27 : $i]:
% 0.58/0.84         (~ (v2_struct_0 @ (k2_yellow_1 @ X27)) | (v1_xboole_0 @ X27))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.58/0.84  thf('68', plain,
% 0.58/0.84      (((r1_tarski @ sk_C @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | (v1_xboole_0 @ sk_A))),
% 0.58/0.84      inference('clc', [status(thm)], ['66', '67'])).
% 0.58/0.84  thf('69', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('70', plain,
% 0.58/0.84      ((r1_tarski @ sk_C @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('clc', [status(thm)], ['68', '69'])).
% 0.58/0.84  thf('71', plain,
% 0.58/0.84      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.58/0.84         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('sup-', [status(thm)], ['3', '16'])).
% 0.58/0.84  thf('72', plain,
% 0.58/0.84      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.58/0.84          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.58/0.84          | ((X12) != (k10_lattice3 @ X11 @ X10 @ X13))
% 0.58/0.84          | (r1_orders_2 @ X11 @ X10 @ X12)
% 0.58/0.84          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.58/0.84          | ~ (l1_orders_2 @ X11)
% 0.58/0.84          | ~ (v1_lattice3 @ X11)
% 0.58/0.84          | ~ (v5_orders_2 @ X11)
% 0.58/0.84          | (v2_struct_0 @ X11))),
% 0.58/0.84      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.58/0.84  thf('73', plain,
% 0.58/0.84      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.58/0.84         ((v2_struct_0 @ X11)
% 0.58/0.84          | ~ (v5_orders_2 @ X11)
% 0.58/0.84          | ~ (v1_lattice3 @ X11)
% 0.58/0.84          | ~ (l1_orders_2 @ X11)
% 0.58/0.84          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.58/0.84          | (r1_orders_2 @ X11 @ X10 @ (k10_lattice3 @ X11 @ X10 @ X13))
% 0.58/0.84          | ~ (m1_subset_1 @ (k10_lattice3 @ X11 @ X10 @ X13) @ 
% 0.58/0.84               (u1_struct_0 @ X11))
% 0.58/0.84          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11)))),
% 0.58/0.84      inference('simplify', [status(thm)], ['72'])).
% 0.58/0.84  thf('74', plain,
% 0.58/0.84      ((~ (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.58/0.84           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.58/0.84        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.58/0.84        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.58/0.84           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.58/0.84        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['71', '73'])).
% 0.58/0.84  thf('75', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('76', plain,
% 0.58/0.84      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.58/0.84        sk_A)),
% 0.58/0.84      inference('sup-', [status(thm)], ['24', '36'])).
% 0.58/0.84  thf('77', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('78', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.84  thf('79', plain,
% 0.58/0.84      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.58/0.84         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('sup-', [status(thm)], ['3', '16'])).
% 0.58/0.84  thf('80', plain,
% 0.58/0.84      (![X28 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X28)) = (X28))),
% 0.58/0.84      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.58/0.84  thf('81', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.84  thf('82', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.58/0.84  thf('83', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('84', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.58/0.84  thf('85', plain,
% 0.58/0.84      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.58/0.84         (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.58/0.84      inference('demod', [status(thm)],
% 0.58/0.84                ['74', '75', '76', '77', '78', '79', '80', '81', '82', '83', 
% 0.58/0.84                 '84'])).
% 0.58/0.84  thf('86', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X1 @ X0)
% 0.58/0.84          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.58/0.84          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.58/0.84          | ~ (m1_subset_1 @ X2 @ X0)
% 0.58/0.84          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.58/0.84  thf('87', plain,
% 0.58/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | ~ (m1_subset_1 @ 
% 0.58/0.84             (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.58/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['85', '86'])).
% 0.58/0.84  thf('88', plain,
% 0.58/0.84      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.58/0.84        sk_A)),
% 0.58/0.84      inference('sup-', [status(thm)], ['24', '36'])).
% 0.58/0.84  thf('89', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.84  thf('90', plain,
% 0.58/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.58/0.84      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.58/0.84  thf('91', plain,
% 0.58/0.84      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.58/0.84         (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.58/0.84      inference('simplify', [status(thm)], ['90'])).
% 0.58/0.84  thf('92', plain,
% 0.58/0.84      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.84         (~ (m1_subset_1 @ X30 @ X31)
% 0.58/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ X31) @ X30 @ X32)
% 0.58/0.84          | (r1_tarski @ X30 @ X32)
% 0.58/0.84          | ~ (m1_subset_1 @ X32 @ X31)
% 0.58/0.84          | (v1_xboole_0 @ X31))),
% 0.58/0.84      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.58/0.84  thf('93', plain,
% 0.58/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v1_xboole_0 @ sk_A)
% 0.58/0.84        | ~ (m1_subset_1 @ 
% 0.58/0.84             (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.58/0.84        | (r1_tarski @ sk_B @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['91', '92'])).
% 0.58/0.84  thf('94', plain,
% 0.58/0.84      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.58/0.84        sk_A)),
% 0.58/0.84      inference('sup-', [status(thm)], ['24', '36'])).
% 0.58/0.84  thf('95', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.58/0.84      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.84  thf('96', plain,
% 0.58/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.58/0.84        | (v1_xboole_0 @ sk_A)
% 0.58/0.84        | (r1_tarski @ sk_B @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.58/0.84      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.58/0.84  thf('97', plain,
% 0.58/0.84      (![X27 : $i]:
% 0.58/0.84         (~ (v2_struct_0 @ (k2_yellow_1 @ X27)) | (v1_xboole_0 @ X27))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.58/0.84  thf('98', plain,
% 0.58/0.84      (((r1_tarski @ sk_B @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84        | (v1_xboole_0 @ sk_A))),
% 0.58/0.84      inference('clc', [status(thm)], ['96', '97'])).
% 0.58/0.84  thf('99', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('100', plain,
% 0.58/0.84      ((r1_tarski @ sk_B @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('clc', [status(thm)], ['98', '99'])).
% 0.58/0.84  thf(t8_xboole_1, axiom,
% 0.58/0.84    (![A:$i,B:$i,C:$i]:
% 0.58/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.58/0.84       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.58/0.84  thf('101', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.58/0.84          | ~ (r1_tarski @ X2 @ X1)
% 0.58/0.84          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.58/0.84      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.58/0.84  thf('102', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 0.58/0.84           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.58/0.84          | ~ (r1_tarski @ X0 @ 
% 0.58/0.84               (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['100', '101'])).
% 0.58/0.84  thf('103', plain,
% 0.58/0.84      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.58/0.84        (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.58/0.84      inference('sup-', [status(thm)], ['70', '102'])).
% 0.58/0.84  thf('104', plain, ($false), inference('demod', [status(thm)], ['18', '103'])).
% 0.58/0.84  
% 0.58/0.84  % SZS output end Refutation
% 0.58/0.84  
% 0.58/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
