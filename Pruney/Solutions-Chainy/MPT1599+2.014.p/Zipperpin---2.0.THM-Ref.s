%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kMOr8ueNkA

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:07 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 486 expanded)
%              Number of leaves         :   30 ( 170 expanded)
%              Depth                    :   17
%              Number of atoms          : 1220 (7267 expanded)
%              Number of equality atoms :   16 (  74 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

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
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k12_lattice3 @ X10 @ X9 @ X11 )
        = ( k11_lattice3 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('6',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

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

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( X14
       != ( k12_lattice3 @ X13 @ X12 @ X15 ) )
      | ( r1_orders_2 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow_0])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( v5_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ ( k12_lattice3 @ X13 @ X12 @ X15 ) @ X15 )
      | ~ ( m1_subset_1 @ ( k12_lattice3 @ X13 @ X12 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k12_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v2_lattice3 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k12_lattice3 @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k12_lattice3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('18',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('23',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('28',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('30',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['12','23','24','25','26','27','28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('35',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('38',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('44',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X26 ) @ X25 @ X27 )
      | ( r1_tarski @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('47',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X24: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X24 ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( X14
       != ( k12_lattice3 @ X13 @ X12 @ X15 ) )
      | ( r1_orders_2 @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow_0])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( v5_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ ( k12_lattice3 @ X13 @ X12 @ X15 ) @ X12 )
      | ~ ( m1_subset_1 @ ( k12_lattice3 @ X13 @ X12 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('65',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('67',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('69',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('73',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X24: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X24 ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['77','78'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['55','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kMOr8ueNkA
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:35:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 305 iterations in 0.346s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.59/0.80  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.59/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.59/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.80  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.59/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.80  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.59/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.59/0.80  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.59/0.80  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.80  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.59/0.80  thf(t7_yellow_1, conjecture,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.80       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.59/0.80         ( ![B:$i]:
% 0.59/0.80           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.80             ( ![C:$i]:
% 0.59/0.80               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.80                 ( r1_tarski @
% 0.59/0.80                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.59/0.80                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i]:
% 0.59/0.80        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.80          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.59/0.80            ( ![B:$i]:
% 0.59/0.80              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.80                ( ![C:$i]:
% 0.59/0.80                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.80                    ( r1_tarski @
% 0.59/0.80                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.59/0.80                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 0.59/0.80  thf('0', plain,
% 0.59/0.80      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('1', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(redefinition_k12_lattice3, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.59/0.80         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.59/0.80         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.59/0.80          | ~ (l1_orders_2 @ X10)
% 0.59/0.80          | ~ (v2_lattice3 @ X10)
% 0.59/0.80          | ~ (v5_orders_2 @ X10)
% 0.59/0.80          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.59/0.80          | ((k12_lattice3 @ X10 @ X9 @ X11) = (k11_lattice3 @ X10 @ X9 @ X11)))),
% 0.59/0.80      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.59/0.80            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.80  thf(fc5_yellow_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.59/0.80       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.59/0.80       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.59/0.80       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.59/0.80  thf('5', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.59/0.80  thf('6', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_k2_yellow_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.59/0.80       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.59/0.80  thf('7', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.59/0.80            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.59/0.80      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf(t23_yellow_0, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.80           ( ![C:$i]:
% 0.59/0.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.80               ( ![D:$i]:
% 0.59/0.80                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.80                   ( ( ( D ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.59/0.80                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.59/0.80                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.59/0.80                       ( ![E:$i]:
% 0.59/0.80                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.80                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.59/0.80                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.59/0.80                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.59/0.80          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.59/0.80          | ((X14) != (k12_lattice3 @ X13 @ X12 @ X15))
% 0.59/0.80          | (r1_orders_2 @ X13 @ X14 @ X15)
% 0.59/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.59/0.80          | ~ (l1_orders_2 @ X13)
% 0.59/0.80          | ~ (v2_lattice3 @ X13)
% 0.59/0.80          | ~ (v5_orders_2 @ X13))),
% 0.59/0.80      inference('cnf', [status(esa)], [t23_yellow_0])).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.59/0.80         (~ (v5_orders_2 @ X13)
% 0.59/0.80          | ~ (v2_lattice3 @ X13)
% 0.59/0.80          | ~ (l1_orders_2 @ X13)
% 0.59/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.59/0.80          | (r1_orders_2 @ X13 @ (k12_lattice3 @ X13 @ X12 @ X15) @ X15)
% 0.59/0.80          | ~ (m1_subset_1 @ (k12_lattice3 @ X13 @ X12 @ X15) @ 
% 0.59/0.80               (u1_struct_0 @ X13))
% 0.59/0.80          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['10'])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      ((~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.59/0.80        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['9', '11'])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_k12_lattice3, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.59/0.80         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.59/0.80         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80       ( m1_subset_1 @ ( k12_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.59/0.80          | ~ (l1_orders_2 @ X7)
% 0.59/0.80          | ~ (v2_lattice3 @ X7)
% 0.59/0.80          | ~ (v5_orders_2 @ X7)
% 0.59/0.80          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.59/0.80          | (m1_subset_1 @ (k12_lattice3 @ X7 @ X6 @ X8) @ (u1_struct_0 @ X7)))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k12_lattice3])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.59/0.80           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('17', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.59/0.80  thf('18', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('19', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.59/0.80           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.59/0.80      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['13', '20'])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('27', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.80  thf('28', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('29', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.59/0.80      inference('demod', [status(thm)],
% 0.59/0.80                ['12', '23', '24', '25', '26', '27', '28', '29'])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['13', '20'])).
% 0.59/0.80  thf(redefinition_r3_orders_2, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.80         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.59/0.80         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.59/0.80          | ~ (l1_orders_2 @ X4)
% 0.59/0.80          | ~ (v3_orders_2 @ X4)
% 0.59/0.80          | (v2_struct_0 @ X4)
% 0.59/0.80          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.59/0.80          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.59/0.80          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.59/0.80      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.59/0.80          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80          | ~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.80  thf('34', plain, (![X21 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X21))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.59/0.80  thf('35', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.59/0.80          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.59/0.80          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['30', '39'])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.59/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['13', '20'])).
% 0.59/0.80  thf(t3_yellow_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.80           ( ![C:$i]:
% 0.59/0.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.59/0.80               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.59/0.80                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k2_yellow_1 @ X26)))
% 0.59/0.80          | ~ (r3_orders_2 @ (k2_yellow_1 @ X26) @ X25 @ X27)
% 0.59/0.80          | (r1_tarski @ X25 @ X27)
% 0.59/0.80          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X26)))
% 0.59/0.80          | (v1_xboole_0 @ X26))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ sk_A)
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80             X0)
% 0.59/0.80          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ sk_A)
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80             X0)
% 0.59/0.80          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.59/0.80  thf('49', plain,
% 0.59/0.80      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           sk_C)
% 0.59/0.80        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | (v1_xboole_0 @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['42', '48'])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           sk_C)
% 0.59/0.80        | (v1_xboole_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['49', '50'])).
% 0.59/0.80  thf(fc6_yellow_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.80       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.59/0.80         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.59/0.80  thf('52', plain,
% 0.59/0.80      (![X24 : $i]:
% 0.59/0.80         (~ (v2_struct_0 @ (k2_yellow_1 @ X24)) | (v1_xboole_0 @ X24))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.59/0.80  thf('53', plain,
% 0.59/0.80      (((v1_xboole_0 @ sk_A)
% 0.59/0.80        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['51', '52'])).
% 0.59/0.80  thf('54', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.59/0.80      inference('clc', [status(thm)], ['53', '54'])).
% 0.59/0.80  thf('56', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf('57', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.59/0.80          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.59/0.80          | ((X14) != (k12_lattice3 @ X13 @ X12 @ X15))
% 0.59/0.80          | (r1_orders_2 @ X13 @ X14 @ X12)
% 0.59/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.59/0.80          | ~ (l1_orders_2 @ X13)
% 0.59/0.80          | ~ (v2_lattice3 @ X13)
% 0.59/0.80          | ~ (v5_orders_2 @ X13))),
% 0.59/0.80      inference('cnf', [status(esa)], [t23_yellow_0])).
% 0.59/0.80  thf('58', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.59/0.80         (~ (v5_orders_2 @ X13)
% 0.59/0.80          | ~ (v2_lattice3 @ X13)
% 0.59/0.80          | ~ (l1_orders_2 @ X13)
% 0.59/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.59/0.80          | (r1_orders_2 @ X13 @ (k12_lattice3 @ X13 @ X12 @ X15) @ X12)
% 0.59/0.80          | ~ (m1_subset_1 @ (k12_lattice3 @ X13 @ X12 @ X15) @ 
% 0.59/0.80               (u1_struct_0 @ X13))
% 0.59/0.80          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['57'])).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      ((~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.59/0.80        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['56', '58'])).
% 0.59/0.80  thf('60', plain,
% 0.59/0.80      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.80  thf('61', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('62', plain,
% 0.59/0.80      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.59/0.80         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '8'])).
% 0.59/0.80  thf('63', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('64', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.59/0.80  thf('65', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('66', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.59/0.80  thf('67', plain,
% 0.59/0.80      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.59/0.80      inference('demod', [status(thm)],
% 0.59/0.80                ['59', '60', '61', '62', '63', '64', '65', '66'])).
% 0.59/0.80  thf('68', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.59/0.80          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.59/0.80  thf('69', plain,
% 0.59/0.80      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.80  thf('70', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('71', plain,
% 0.59/0.80      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['69', '70'])).
% 0.59/0.80  thf('72', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ sk_A)
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80             X0)
% 0.59/0.80          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.59/0.80               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.59/0.80  thf('73', plain,
% 0.59/0.80      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           sk_B)
% 0.59/0.80        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.59/0.80        | (v1_xboole_0 @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['71', '72'])).
% 0.59/0.80  thf('74', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('75', plain,
% 0.59/0.80      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.59/0.80        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           sk_B)
% 0.59/0.80        | (v1_xboole_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['73', '74'])).
% 0.59/0.80  thf('76', plain,
% 0.59/0.80      (![X24 : $i]:
% 0.59/0.80         (~ (v2_struct_0 @ (k2_yellow_1 @ X24)) | (v1_xboole_0 @ X24))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.59/0.80  thf('77', plain,
% 0.59/0.80      (((v1_xboole_0 @ sk_A)
% 0.59/0.80        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           sk_B))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('78', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('79', plain,
% 0.59/0.80      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.59/0.80      inference('clc', [status(thm)], ['77', '78'])).
% 0.59/0.80  thf(t19_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.59/0.80       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.80  thf('80', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.59/0.80          | ~ (r1_tarski @ X0 @ X2)
% 0.59/0.80          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.59/0.80  thf('81', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80           (k3_xboole_0 @ sk_B @ X0))
% 0.59/0.80          | ~ (r1_tarski @ 
% 0.59/0.80               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['79', '80'])).
% 0.59/0.80  thf('82', plain,
% 0.59/0.80      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.80        (k3_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['55', '81'])).
% 0.59/0.80  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
