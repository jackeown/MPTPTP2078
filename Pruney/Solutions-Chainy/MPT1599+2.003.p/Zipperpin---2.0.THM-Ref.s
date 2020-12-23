%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wXA4glbHdt

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:06 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 313 expanded)
%              Number of leaves         :   31 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          : 1208 (4528 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k12_lattice3 @ X14 @ X13 @ X15 )
        = ( k11_lattice3 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('5',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','7'])).

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

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( X18
       != ( k12_lattice3 @ X17 @ X16 @ X19 ) )
      | ( r1_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow_0])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( v5_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ ( k12_lattice3 @ X17 @ X16 @ X19 ) @ X19 )
      | ~ ( m1_subset_1 @ ( k12_lattice3 @ X17 @ X16 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X11 @ X10 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('23',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('25',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['11','18','19','20','21','22','23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X24: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('30',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X28 ) @ X27 @ X29 )
      | ( r1_tarski @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k12_lattice3 @ A @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( ( k12_lattice3 @ X8 @ X7 @ X9 )
        = ( k12_lattice3 @ X8 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k12_lattice3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('48',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('53',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( v5_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ ( k12_lattice3 @ X17 @ X16 @ X19 ) @ X19 )
      | ~ ( m1_subset_1 @ ( k12_lattice3 @ X17 @ X16 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('55',plain,
    ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('61',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('63',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['55','56','57','58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('69',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','75'])).

thf('77',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('81',plain,(
    ! [X6: $i] :
      ( ~ ( v2_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wXA4glbHdt
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.90  % Solved by: fo/fo7.sh
% 0.69/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.90  % done 291 iterations in 0.446s
% 0.69/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.90  % SZS output start Refutation
% 0.69/0.90  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.69/0.90  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.69/0.90  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.69/0.90  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.69/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.90  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.69/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.90  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.69/0.90  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.69/0.90  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.69/0.90  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.69/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.90  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.69/0.90  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.69/0.90  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.69/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.90  thf(t7_yellow_1, conjecture,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.90       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.69/0.90         ( ![B:$i]:
% 0.69/0.90           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.90             ( ![C:$i]:
% 0.69/0.90               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.90                 ( r1_tarski @
% 0.69/0.90                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.69/0.90                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.69/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.90    (~( ![A:$i]:
% 0.69/0.90        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.90          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.69/0.90            ( ![B:$i]:
% 0.69/0.90              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.90                ( ![C:$i]:
% 0.69/0.90                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.90                    ( r1_tarski @
% 0.69/0.90                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.69/0.90                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.69/0.90    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 0.69/0.90  thf('0', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('1', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(redefinition_k12_lattice3, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.69/0.90         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.69/0.90         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.69/0.90  thf('2', plain,
% 0.69/0.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.69/0.90          | ~ (l1_orders_2 @ X14)
% 0.69/0.90          | ~ (v2_lattice3 @ X14)
% 0.69/0.90          | ~ (v5_orders_2 @ X14)
% 0.69/0.90          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.69/0.90          | ((k12_lattice3 @ X14 @ X13 @ X15)
% 0.69/0.90              = (k11_lattice3 @ X14 @ X13 @ X15)))),
% 0.69/0.90      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.69/0.90  thf('3', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.69/0.90            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.90  thf(fc5_yellow_1, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.69/0.90       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.69/0.90       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.69/0.90       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.69/0.90  thf('4', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.90  thf('5', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(dt_k2_yellow_1, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.69/0.90       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.69/0.90  thf('6', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.90  thf('7', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.69/0.90            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.69/0.90      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.69/0.90  thf('8', plain,
% 0.69/0.90      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.90         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.69/0.90      inference('sup-', [status(thm)], ['0', '7'])).
% 0.69/0.90  thf(t23_yellow_0, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.90           ( ![C:$i]:
% 0.69/0.90             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.90               ( ![D:$i]:
% 0.69/0.90                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.90                   ( ( ( D ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.69/0.90                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.69/0.90                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.69/0.90                       ( ![E:$i]:
% 0.69/0.90                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.90                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.69/0.90                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.69/0.90                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.90  thf('9', plain,
% 0.69/0.90      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.69/0.90          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.69/0.90          | ((X18) != (k12_lattice3 @ X17 @ X16 @ X19))
% 0.69/0.90          | (r1_orders_2 @ X17 @ X18 @ X19)
% 0.69/0.90          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.69/0.90          | ~ (l1_orders_2 @ X17)
% 0.69/0.90          | ~ (v2_lattice3 @ X17)
% 0.69/0.90          | ~ (v5_orders_2 @ X17))),
% 0.69/0.90      inference('cnf', [status(esa)], [t23_yellow_0])).
% 0.69/0.90  thf('10', plain,
% 0.69/0.90      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.69/0.90         (~ (v5_orders_2 @ X17)
% 0.69/0.90          | ~ (v2_lattice3 @ X17)
% 0.69/0.90          | ~ (l1_orders_2 @ X17)
% 0.69/0.90          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.69/0.90          | (r1_orders_2 @ X17 @ (k12_lattice3 @ X17 @ X16 @ X19) @ X19)
% 0.69/0.90          | ~ (m1_subset_1 @ (k12_lattice3 @ X17 @ X16 @ X19) @ 
% 0.69/0.90               (u1_struct_0 @ X17))
% 0.69/0.90          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['9'])).
% 0.69/0.90  thf('11', plain,
% 0.69/0.90      ((~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.69/0.90        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['8', '10'])).
% 0.69/0.90  thf('12', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('13', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(dt_k11_lattice3, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.69/0.90         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.69/0.90  thf('14', plain,
% 0.69/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.69/0.90          | ~ (l1_orders_2 @ X11)
% 0.69/0.90          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.69/0.90          | (m1_subset_1 @ (k11_lattice3 @ X11 @ X10 @ X12) @ 
% 0.69/0.90             (u1_struct_0 @ X11)))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 0.69/0.90  thf('15', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.69/0.90           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['13', '14'])).
% 0.69/0.90  thf('16', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.90  thf('17', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.69/0.90           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.69/0.90      inference('demod', [status(thm)], ['15', '16'])).
% 0.69/0.90  thf('18', plain,
% 0.69/0.90      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['12', '17'])).
% 0.69/0.90  thf('19', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('20', plain,
% 0.69/0.90      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.90         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.69/0.90      inference('sup-', [status(thm)], ['0', '7'])).
% 0.69/0.90  thf('21', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('22', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.90  thf('23', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('24', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.90  thf('25', plain,
% 0.69/0.90      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.69/0.90      inference('demod', [status(thm)],
% 0.69/0.90                ['11', '18', '19', '20', '21', '22', '23', '24'])).
% 0.69/0.90  thf('26', plain,
% 0.69/0.90      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['12', '17'])).
% 0.69/0.90  thf(redefinition_r3_orders_2, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.69/0.90         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.69/0.90         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.69/0.90  thf('27', plain,
% 0.69/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.69/0.90          | ~ (l1_orders_2 @ X4)
% 0.69/0.90          | ~ (v3_orders_2 @ X4)
% 0.69/0.90          | (v2_struct_0 @ X4)
% 0.69/0.90          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.69/0.90          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.69/0.90          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.69/0.90      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.69/0.90  thf('28', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.69/0.90          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90          | ~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.90  thf('29', plain, (![X24 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X24))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.90  thf('30', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.90  thf('31', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.69/0.90          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.69/0.90  thf('32', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.69/0.90      inference('sup-', [status(thm)], ['25', '31'])).
% 0.69/0.90  thf('33', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('34', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.69/0.90      inference('demod', [status(thm)], ['32', '33'])).
% 0.69/0.90  thf('35', plain,
% 0.69/0.90      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['12', '17'])).
% 0.69/0.90  thf(t3_yellow_1, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.90           ( ![C:$i]:
% 0.69/0.90             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.69/0.90               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.69/0.90                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.69/0.90  thf('36', plain,
% 0.69/0.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.69/0.90          | ~ (r3_orders_2 @ (k2_yellow_1 @ X28) @ X27 @ X29)
% 0.69/0.90          | (r1_tarski @ X27 @ X29)
% 0.69/0.90          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ (k2_yellow_1 @ X28)))
% 0.69/0.90          | (v1_xboole_0 @ X28))),
% 0.69/0.90      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.69/0.90  thf('37', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ sk_A)
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90             X0)
% 0.69/0.90          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['35', '36'])).
% 0.69/0.90  thf('38', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90           sk_C)
% 0.69/0.90        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | (v1_xboole_0 @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['34', '37'])).
% 0.69/0.90  thf('39', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('40', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90           sk_C)
% 0.69/0.90        | (v1_xboole_0 @ sk_A))),
% 0.69/0.90      inference('demod', [status(thm)], ['38', '39'])).
% 0.69/0.90  thf('41', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('42', plain,
% 0.69/0.90      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.69/0.90        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('clc', [status(thm)], ['40', '41'])).
% 0.69/0.90  thf('43', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('44', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(commutativity_k12_lattice3, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.69/0.90         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.69/0.90         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90       ( ( k12_lattice3 @ A @ B @ C ) = ( k12_lattice3 @ A @ C @ B ) ) ))).
% 0.69/0.90  thf('45', plain,
% 0.69/0.90      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.69/0.90          | ~ (l1_orders_2 @ X8)
% 0.69/0.90          | ~ (v2_lattice3 @ X8)
% 0.69/0.90          | ~ (v5_orders_2 @ X8)
% 0.69/0.90          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.69/0.90          | ((k12_lattice3 @ X8 @ X7 @ X9) = (k12_lattice3 @ X8 @ X9 @ X7)))),
% 0.69/0.90      inference('cnf', [status(esa)], [commutativity_k12_lattice3])).
% 0.69/0.90  thf('46', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.69/0.90            = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['44', '45'])).
% 0.69/0.90  thf('47', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.90  thf('48', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('49', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.90  thf('50', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.69/0.90            = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.69/0.90      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.69/0.90  thf('51', plain,
% 0.69/0.90      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.90         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 0.69/0.90      inference('sup-', [status(thm)], ['43', '50'])).
% 0.69/0.90  thf('52', plain,
% 0.69/0.90      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.90         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.69/0.90      inference('sup-', [status(thm)], ['0', '7'])).
% 0.69/0.90  thf('53', plain,
% 0.69/0.90      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.90         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 0.69/0.90      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.90  thf('54', plain,
% 0.69/0.90      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.69/0.90         (~ (v5_orders_2 @ X17)
% 0.69/0.90          | ~ (v2_lattice3 @ X17)
% 0.69/0.90          | ~ (l1_orders_2 @ X17)
% 0.69/0.90          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.69/0.90          | (r1_orders_2 @ X17 @ (k12_lattice3 @ X17 @ X16 @ X19) @ X19)
% 0.69/0.90          | ~ (m1_subset_1 @ (k12_lattice3 @ X17 @ X16 @ X19) @ 
% 0.69/0.90               (u1_struct_0 @ X17))
% 0.69/0.90          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['9'])).
% 0.69/0.90  thf('55', plain,
% 0.69/0.90      ((~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B)
% 0.69/0.90        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['53', '54'])).
% 0.69/0.90  thf('56', plain,
% 0.69/0.90      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['12', '17'])).
% 0.69/0.90  thf('57', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('58', plain,
% 0.69/0.90      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.69/0.90         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 0.69/0.90      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.90  thf('59', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('60', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.90  thf('61', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('62', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.69/0.90  thf('63', plain,
% 0.69/0.90      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.69/0.90      inference('demod', [status(thm)],
% 0.69/0.90                ['55', '56', '57', '58', '59', '60', '61', '62'])).
% 0.69/0.90  thf('64', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.69/0.90          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.69/0.90  thf('65', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.69/0.90      inference('sup-', [status(thm)], ['63', '64'])).
% 0.69/0.90  thf('66', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('67', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.69/0.90      inference('demod', [status(thm)], ['65', '66'])).
% 0.69/0.90  thf('68', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ sk_A)
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90             X0)
% 0.69/0.90          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.69/0.90               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['35', '36'])).
% 0.69/0.90  thf('69', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90           sk_B)
% 0.69/0.90        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.69/0.90        | (v1_xboole_0 @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['67', '68'])).
% 0.69/0.90  thf('70', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('71', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90           sk_B)
% 0.69/0.90        | (v1_xboole_0 @ sk_A))),
% 0.69/0.90      inference('demod', [status(thm)], ['69', '70'])).
% 0.69/0.90  thf('72', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('73', plain,
% 0.69/0.90      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.69/0.90        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('clc', [status(thm)], ['71', '72'])).
% 0.69/0.90  thf(t19_xboole_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.69/0.90       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.69/0.90  thf('74', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.90         (~ (r1_tarski @ X0 @ X1)
% 0.69/0.90          | ~ (r1_tarski @ X0 @ X2)
% 0.69/0.90          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.69/0.90  thf('75', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90             (k3_xboole_0 @ sk_B @ X0))
% 0.69/0.90          | ~ (r1_tarski @ 
% 0.69/0.90               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['73', '74'])).
% 0.69/0.90  thf('76', plain,
% 0.69/0.90      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.69/0.90        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90           (k3_xboole_0 @ sk_B @ sk_C))
% 0.69/0.90        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['42', '75'])).
% 0.69/0.90  thf('77', plain,
% 0.69/0.90      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90         (k3_xboole_0 @ sk_B @ sk_C))
% 0.69/0.90        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['76'])).
% 0.69/0.90  thf('78', plain,
% 0.69/0.90      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.90          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('79', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.90      inference('clc', [status(thm)], ['77', '78'])).
% 0.69/0.90  thf('80', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.69/0.90  thf(cc2_lattice3, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( l1_orders_2 @ A ) =>
% 0.69/0.90       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.69/0.90  thf('81', plain,
% 0.69/0.90      (![X6 : $i]:
% 0.69/0.90         (~ (v2_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.69/0.90      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.69/0.90  thf('82', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.69/0.90          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['80', '81'])).
% 0.69/0.90  thf('83', plain, (~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['79', '82'])).
% 0.69/0.90  thf('84', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('85', plain, ($false), inference('demod', [status(thm)], ['83', '84'])).
% 0.69/0.90  
% 0.69/0.90  % SZS output end Refutation
% 0.69/0.90  
% 0.69/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
