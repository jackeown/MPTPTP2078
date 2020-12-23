%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y3CU5AyIwo

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:08 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 270 expanded)
%              Number of leaves         :   30 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          : 1087 (3881 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('6',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
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

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('24',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('26',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['12','19','20','21','22','23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('31',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X25 ) @ X24 @ X26 )
      | ( r1_tarski @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X23: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X23 ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( v5_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ ( k12_lattice3 @ X13 @ X12 @ X15 ) @ X12 )
      | ~ ( m1_subset_1 @ ( k12_lattice3 @ X13 @ X12 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X18: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('55',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X22: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('57',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['49','50','51','52','53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('59',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X23: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X23 ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['67','68'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['45','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y3CU5AyIwo
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 09:57:57 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.55/1.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.55/1.77  % Solved by: fo/fo7.sh
% 1.55/1.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.55/1.77  % done 458 iterations in 1.292s
% 1.55/1.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.55/1.77  % SZS output start Refutation
% 1.55/1.77  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.55/1.77  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 1.55/1.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.55/1.77  thf(sk_C_type, type, sk_C: $i).
% 1.55/1.77  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 1.55/1.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.55/1.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.55/1.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.55/1.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.55/1.77  thf(sk_B_type, type, sk_B: $i).
% 1.55/1.77  thf(sk_A_type, type, sk_A: $i).
% 1.55/1.77  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 1.55/1.77  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 1.55/1.77  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.55/1.77  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.55/1.77  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.55/1.77  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.55/1.77  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 1.55/1.77  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 1.55/1.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.55/1.77  thf(t7_yellow_1, conjecture,
% 1.55/1.77    (![A:$i]:
% 1.55/1.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.55/1.77       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 1.55/1.77         ( ![B:$i]:
% 1.55/1.77           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 1.55/1.77             ( ![C:$i]:
% 1.55/1.77               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 1.55/1.77                 ( r1_tarski @
% 1.55/1.77                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 1.55/1.77                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 1.55/1.77  thf(zf_stmt_0, negated_conjecture,
% 1.55/1.77    (~( ![A:$i]:
% 1.55/1.77        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.55/1.77          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 1.55/1.77            ( ![B:$i]:
% 1.55/1.77              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 1.55/1.77                ( ![C:$i]:
% 1.55/1.77                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 1.55/1.77                    ( r1_tarski @
% 1.55/1.77                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 1.55/1.77                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 1.55/1.77    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 1.55/1.77  thf('0', plain,
% 1.55/1.77      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77          (k3_xboole_0 @ sk_B @ sk_C))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('1', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('2', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf(redefinition_k12_lattice3, axiom,
% 1.55/1.77    (![A:$i,B:$i,C:$i]:
% 1.55/1.77     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 1.55/1.77         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.55/1.77         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.55/1.77       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 1.55/1.77  thf('3', plain,
% 1.55/1.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.55/1.77         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 1.55/1.77          | ~ (l1_orders_2 @ X10)
% 1.55/1.77          | ~ (v2_lattice3 @ X10)
% 1.55/1.77          | ~ (v5_orders_2 @ X10)
% 1.55/1.77          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 1.55/1.77          | ((k12_lattice3 @ X10 @ X9 @ X11) = (k11_lattice3 @ X10 @ X9 @ X11)))),
% 1.55/1.77      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 1.55/1.77  thf('4', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 1.55/1.77            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['2', '3'])).
% 1.55/1.77  thf(fc5_yellow_1, axiom,
% 1.55/1.77    (![A:$i]:
% 1.55/1.77     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 1.55/1.77       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 1.55/1.77       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 1.55/1.77       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 1.55/1.77  thf('5', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 1.55/1.77      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 1.55/1.77  thf('6', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf(dt_k2_yellow_1, axiom,
% 1.55/1.77    (![A:$i]:
% 1.55/1.77     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 1.55/1.77       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 1.55/1.77  thf('7', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 1.55/1.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 1.55/1.77  thf('8', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 1.55/1.77            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0))
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 1.55/1.77      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.55/1.77  thf('9', plain,
% 1.55/1.77      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 1.55/1.77         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 1.55/1.77      inference('sup-', [status(thm)], ['1', '8'])).
% 1.55/1.77  thf(t23_yellow_0, axiom,
% 1.55/1.77    (![A:$i]:
% 1.55/1.77     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.55/1.77       ( ![B:$i]:
% 1.55/1.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.55/1.77           ( ![C:$i]:
% 1.55/1.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.55/1.77               ( ![D:$i]:
% 1.55/1.77                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.55/1.77                   ( ( ( D ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 1.55/1.77                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 1.55/1.77                       ( r1_orders_2 @ A @ D @ C ) & 
% 1.55/1.77                       ( ![E:$i]:
% 1.55/1.77                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 1.55/1.77                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 1.55/1.77                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 1.55/1.77                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.55/1.77  thf('10', plain,
% 1.55/1.77      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.55/1.77         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.55/1.77          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 1.55/1.77          | ((X14) != (k12_lattice3 @ X13 @ X12 @ X15))
% 1.55/1.77          | (r1_orders_2 @ X13 @ X14 @ X15)
% 1.55/1.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 1.55/1.77          | ~ (l1_orders_2 @ X13)
% 1.55/1.77          | ~ (v2_lattice3 @ X13)
% 1.55/1.77          | ~ (v5_orders_2 @ X13))),
% 1.55/1.77      inference('cnf', [status(esa)], [t23_yellow_0])).
% 1.55/1.77  thf('11', plain,
% 1.55/1.77      (![X12 : $i, X13 : $i, X15 : $i]:
% 1.55/1.77         (~ (v5_orders_2 @ X13)
% 1.55/1.77          | ~ (v2_lattice3 @ X13)
% 1.55/1.77          | ~ (l1_orders_2 @ X13)
% 1.55/1.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 1.55/1.77          | (r1_orders_2 @ X13 @ (k12_lattice3 @ X13 @ X12 @ X15) @ X15)
% 1.55/1.77          | ~ (m1_subset_1 @ (k12_lattice3 @ X13 @ X12 @ X15) @ 
% 1.55/1.77               (u1_struct_0 @ X13))
% 1.55/1.77          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13)))),
% 1.55/1.77      inference('simplify', [status(thm)], ['10'])).
% 1.55/1.77  thf('12', plain,
% 1.55/1.77      ((~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 1.55/1.77        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['9', '11'])).
% 1.55/1.77  thf('13', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('14', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf(dt_k11_lattice3, axiom,
% 1.55/1.77    (![A:$i,B:$i,C:$i]:
% 1.55/1.77     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.55/1.77         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.55/1.77       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 1.55/1.77  thf('15', plain,
% 1.55/1.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.55/1.77         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 1.55/1.77          | ~ (l1_orders_2 @ X7)
% 1.55/1.77          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 1.55/1.77          | (m1_subset_1 @ (k11_lattice3 @ X7 @ X6 @ X8) @ (u1_struct_0 @ X7)))),
% 1.55/1.77      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 1.55/1.77  thf('16', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 1.55/1.77           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['14', '15'])).
% 1.55/1.77  thf('17', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 1.55/1.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 1.55/1.77  thf('18', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 1.55/1.77           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 1.55/1.77      inference('demod', [status(thm)], ['16', '17'])).
% 1.55/1.77  thf('19', plain,
% 1.55/1.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['13', '18'])).
% 1.55/1.77  thf('20', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('21', plain,
% 1.55/1.77      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 1.55/1.77         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 1.55/1.77      inference('sup-', [status(thm)], ['1', '8'])).
% 1.55/1.77  thf('22', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('23', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 1.55/1.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 1.55/1.77  thf('24', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('25', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 1.55/1.77      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 1.55/1.77  thf('26', plain,
% 1.55/1.77      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 1.55/1.77      inference('demod', [status(thm)],
% 1.55/1.77                ['12', '19', '20', '21', '22', '23', '24', '25'])).
% 1.55/1.77  thf('27', plain,
% 1.55/1.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['13', '18'])).
% 1.55/1.77  thf(redefinition_r3_orders_2, axiom,
% 1.55/1.77    (![A:$i,B:$i,C:$i]:
% 1.55/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.55/1.77         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.55/1.77         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.55/1.77       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 1.55/1.77  thf('28', plain,
% 1.55/1.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.55/1.77         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 1.55/1.77          | ~ (l1_orders_2 @ X4)
% 1.55/1.77          | ~ (v3_orders_2 @ X4)
% 1.55/1.77          | (v2_struct_0 @ X4)
% 1.55/1.77          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 1.55/1.77          | (r3_orders_2 @ X4 @ X3 @ X5)
% 1.55/1.77          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 1.55/1.77      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 1.55/1.77  thf('29', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 1.55/1.77          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77          | ~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['27', '28'])).
% 1.55/1.77  thf('30', plain, (![X20 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X20))),
% 1.55/1.77      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 1.55/1.77  thf('31', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 1.55/1.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 1.55/1.77  thf('32', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 1.55/1.77          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.55/1.77  thf('33', plain,
% 1.55/1.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 1.55/1.77      inference('sup-', [status(thm)], ['26', '32'])).
% 1.55/1.77  thf('34', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('35', plain,
% 1.55/1.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 1.55/1.77      inference('demod', [status(thm)], ['33', '34'])).
% 1.55/1.77  thf('36', plain,
% 1.55/1.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['13', '18'])).
% 1.55/1.77  thf(t3_yellow_1, axiom,
% 1.55/1.77    (![A:$i]:
% 1.55/1.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.55/1.77       ( ![B:$i]:
% 1.55/1.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 1.55/1.77           ( ![C:$i]:
% 1.55/1.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 1.55/1.77               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 1.55/1.77                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 1.55/1.77  thf('37', plain,
% 1.55/1.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.55/1.77         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k2_yellow_1 @ X25)))
% 1.55/1.77          | ~ (r3_orders_2 @ (k2_yellow_1 @ X25) @ X24 @ X26)
% 1.55/1.77          | (r1_tarski @ X24 @ X26)
% 1.55/1.77          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ (k2_yellow_1 @ X25)))
% 1.55/1.77          | (v1_xboole_0 @ X25))),
% 1.55/1.77      inference('cnf', [status(esa)], [t3_yellow_1])).
% 1.55/1.77  thf('38', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         ((v1_xboole_0 @ sk_A)
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77             X0)
% 1.55/1.77          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 1.55/1.77      inference('sup-', [status(thm)], ['36', '37'])).
% 1.55/1.77  thf('39', plain,
% 1.55/1.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           sk_C)
% 1.55/1.77        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | (v1_xboole_0 @ sk_A))),
% 1.55/1.77      inference('sup-', [status(thm)], ['35', '38'])).
% 1.55/1.77  thf('40', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('41', plain,
% 1.55/1.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           sk_C)
% 1.55/1.77        | (v1_xboole_0 @ sk_A))),
% 1.55/1.77      inference('demod', [status(thm)], ['39', '40'])).
% 1.55/1.77  thf(fc6_yellow_1, axiom,
% 1.55/1.77    (![A:$i]:
% 1.55/1.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.55/1.77       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 1.55/1.77         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 1.55/1.77  thf('42', plain,
% 1.55/1.77      (![X23 : $i]:
% 1.55/1.77         (~ (v2_struct_0 @ (k2_yellow_1 @ X23)) | (v1_xboole_0 @ X23))),
% 1.55/1.77      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 1.55/1.77  thf('43', plain,
% 1.55/1.77      (((v1_xboole_0 @ sk_A)
% 1.55/1.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           sk_C))),
% 1.55/1.77      inference('clc', [status(thm)], ['41', '42'])).
% 1.55/1.77  thf('44', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('45', plain,
% 1.55/1.77      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 1.55/1.77      inference('clc', [status(thm)], ['43', '44'])).
% 1.55/1.77  thf('46', plain,
% 1.55/1.77      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 1.55/1.77         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 1.55/1.77      inference('sup-', [status(thm)], ['1', '8'])).
% 1.55/1.77  thf('47', plain,
% 1.55/1.77      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.55/1.77         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.55/1.77          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 1.55/1.77          | ((X14) != (k12_lattice3 @ X13 @ X12 @ X15))
% 1.55/1.77          | (r1_orders_2 @ X13 @ X14 @ X12)
% 1.55/1.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 1.55/1.77          | ~ (l1_orders_2 @ X13)
% 1.55/1.77          | ~ (v2_lattice3 @ X13)
% 1.55/1.77          | ~ (v5_orders_2 @ X13))),
% 1.55/1.77      inference('cnf', [status(esa)], [t23_yellow_0])).
% 1.55/1.77  thf('48', plain,
% 1.55/1.77      (![X12 : $i, X13 : $i, X15 : $i]:
% 1.55/1.77         (~ (v5_orders_2 @ X13)
% 1.55/1.77          | ~ (v2_lattice3 @ X13)
% 1.55/1.77          | ~ (l1_orders_2 @ X13)
% 1.55/1.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 1.55/1.77          | (r1_orders_2 @ X13 @ (k12_lattice3 @ X13 @ X12 @ X15) @ X12)
% 1.55/1.77          | ~ (m1_subset_1 @ (k12_lattice3 @ X13 @ X12 @ X15) @ 
% 1.55/1.77               (u1_struct_0 @ X13))
% 1.55/1.77          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13)))),
% 1.55/1.77      inference('simplify', [status(thm)], ['47'])).
% 1.55/1.77  thf('49', plain,
% 1.55/1.77      ((~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 1.55/1.77        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['46', '48'])).
% 1.55/1.77  thf('50', plain,
% 1.55/1.77      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('sup-', [status(thm)], ['13', '18'])).
% 1.55/1.77  thf('51', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('52', plain,
% 1.55/1.77      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 1.55/1.77         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 1.55/1.77      inference('sup-', [status(thm)], ['1', '8'])).
% 1.55/1.77  thf('53', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('54', plain, (![X18 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X18))),
% 1.55/1.77      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 1.55/1.77  thf('55', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('56', plain, (![X22 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X22))),
% 1.55/1.77      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 1.55/1.77  thf('57', plain,
% 1.55/1.77      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 1.55/1.77      inference('demod', [status(thm)],
% 1.55/1.77                ['49', '50', '51', '52', '53', '54', '55', '56'])).
% 1.55/1.77  thf('58', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 1.55/1.77          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.55/1.77  thf('59', plain,
% 1.55/1.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 1.55/1.77      inference('sup-', [status(thm)], ['57', '58'])).
% 1.55/1.77  thf('60', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('61', plain,
% 1.55/1.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 1.55/1.77      inference('demod', [status(thm)], ['59', '60'])).
% 1.55/1.77  thf('62', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         ((v1_xboole_0 @ sk_A)
% 1.55/1.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77             X0)
% 1.55/1.77          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 1.55/1.77               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 1.55/1.77      inference('sup-', [status(thm)], ['36', '37'])).
% 1.55/1.77  thf('63', plain,
% 1.55/1.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           sk_B)
% 1.55/1.77        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 1.55/1.77        | (v1_xboole_0 @ sk_A))),
% 1.55/1.77      inference('sup-', [status(thm)], ['61', '62'])).
% 1.55/1.77  thf('64', plain,
% 1.55/1.77      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('65', plain,
% 1.55/1.77      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 1.55/1.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           sk_B)
% 1.55/1.77        | (v1_xboole_0 @ sk_A))),
% 1.55/1.77      inference('demod', [status(thm)], ['63', '64'])).
% 1.55/1.77  thf('66', plain,
% 1.55/1.77      (![X23 : $i]:
% 1.55/1.77         (~ (v2_struct_0 @ (k2_yellow_1 @ X23)) | (v1_xboole_0 @ X23))),
% 1.55/1.77      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 1.55/1.77  thf('67', plain,
% 1.55/1.77      (((v1_xboole_0 @ sk_A)
% 1.55/1.77        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           sk_B))),
% 1.55/1.77      inference('clc', [status(thm)], ['65', '66'])).
% 1.55/1.77  thf('68', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.55/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.55/1.77  thf('69', plain,
% 1.55/1.77      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 1.55/1.77      inference('clc', [status(thm)], ['67', '68'])).
% 1.55/1.77  thf(t19_xboole_1, axiom,
% 1.55/1.77    (![A:$i,B:$i,C:$i]:
% 1.55/1.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.55/1.77       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.55/1.77  thf('70', plain,
% 1.55/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.55/1.77         (~ (r1_tarski @ X0 @ X1)
% 1.55/1.77          | ~ (r1_tarski @ X0 @ X2)
% 1.55/1.77          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.55/1.77      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.55/1.77  thf('71', plain,
% 1.55/1.77      (![X0 : $i]:
% 1.55/1.77         ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77           (k3_xboole_0 @ sk_B @ X0))
% 1.55/1.77          | ~ (r1_tarski @ 
% 1.55/1.77               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 1.55/1.77      inference('sup-', [status(thm)], ['69', '70'])).
% 1.55/1.77  thf('72', plain,
% 1.55/1.77      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 1.55/1.77        (k3_xboole_0 @ sk_B @ sk_C))),
% 1.55/1.77      inference('sup-', [status(thm)], ['45', '71'])).
% 1.55/1.77  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 1.55/1.77  
% 1.55/1.77  % SZS output end Refutation
% 1.55/1.77  
% 1.55/1.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
