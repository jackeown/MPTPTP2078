%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.00LSayLEDB

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:07 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 218 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          : 1103 (3095 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

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

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( X11
       != ( k11_lattice3 @ X10 @ X9 @ X12 ) )
      | ( r1_orders_2 @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ ( k11_lattice3 @ X10 @ X9 @ X12 ) @ X9 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X10 @ X9 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('14',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('16',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X21: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('21',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X26 ) @ X25 @ X27 )
      | ( r1_tarski @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X24: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X24 ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( X11
       != ( k11_lattice3 @ X10 @ X9 @ X12 ) )
      | ( r1_orders_2 @ X10 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ ( k11_lattice3 @ X10 @ X9 @ X12 ) @ X12 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X10 @ X9 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('44',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('46',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('48',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('53',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X24: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X24 ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['57','58'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['36','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_lattice3,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k11_lattice3 @ A @ B @ C )
                = ( k11_lattice3 @ A @ C @ B ) ) ) ) ) )).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( ( k11_lattice3 @ X15 @ X14 @ X16 )
        = ( k11_lattice3 @ X15 @ X16 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v2_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t15_lattice3])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X23: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('68',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X19: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.00LSayLEDB
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:58:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.62/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.84  % Solved by: fo/fo7.sh
% 0.62/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.84  % done 208 iterations in 0.390s
% 0.62/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.84  % SZS output start Refutation
% 0.62/0.84  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.62/0.84  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.62/0.84  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.62/0.84  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.62/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.62/0.84  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.62/0.84  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.62/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.84  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.62/0.84  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.62/0.84  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.62/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.84  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.62/0.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.62/0.84  thf(t7_yellow_1, conjecture,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.62/0.84       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.62/0.84         ( ![B:$i]:
% 0.62/0.84           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.62/0.84             ( ![C:$i]:
% 0.62/0.84               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.62/0.84                 ( r1_tarski @
% 0.62/0.84                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.62/0.84                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.62/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.84    (~( ![A:$i]:
% 0.62/0.84        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.62/0.84          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.62/0.84            ( ![B:$i]:
% 0.62/0.84              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.62/0.84                ( ![C:$i]:
% 0.62/0.84                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.62/0.84                    ( r1_tarski @
% 0.62/0.84                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.62/0.84                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.62/0.84    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 0.62/0.84  thf('0', plain,
% 0.62/0.84      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.62/0.84          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('1', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('2', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(dt_k11_lattice3, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.62/0.84         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.62/0.84  thf('3', plain,
% 0.62/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.62/0.84          | ~ (l1_orders_2 @ X7)
% 0.62/0.84          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.62/0.84          | (m1_subset_1 @ (k11_lattice3 @ X7 @ X6 @ X8) @ (u1_struct_0 @ X7)))),
% 0.62/0.84      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 0.62/0.84  thf('4', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ 
% 0.62/0.84           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.84  thf(dt_k2_yellow_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.62/0.84       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.62/0.84  thf('5', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.62/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.62/0.84  thf('6', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ 
% 0.62/0.84           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.62/0.84      inference('demod', [status(thm)], ['4', '5'])).
% 0.62/0.84  thf('7', plain,
% 0.62/0.84      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['1', '6'])).
% 0.62/0.84  thf(l28_lattice3, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.62/0.84         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.84           ( ![C:$i]:
% 0.62/0.84             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.84               ( ![D:$i]:
% 0.62/0.84                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.84                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 0.62/0.84                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.62/0.84                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.62/0.84                       ( ![E:$i]:
% 0.62/0.84                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.84                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.62/0.84                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.62/0.84                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.62/0.84  thf('8', plain,
% 0.62/0.84      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.62/0.84          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.62/0.84          | ((X11) != (k11_lattice3 @ X10 @ X9 @ X12))
% 0.62/0.84          | (r1_orders_2 @ X10 @ X11 @ X9)
% 0.62/0.84          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.62/0.84          | ~ (l1_orders_2 @ X10)
% 0.62/0.84          | ~ (v2_lattice3 @ X10)
% 0.62/0.84          | ~ (v5_orders_2 @ X10)
% 0.62/0.84          | (v2_struct_0 @ X10))),
% 0.62/0.84      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.62/0.84  thf('9', plain,
% 0.62/0.84      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.62/0.84         ((v2_struct_0 @ X10)
% 0.62/0.84          | ~ (v5_orders_2 @ X10)
% 0.62/0.84          | ~ (v2_lattice3 @ X10)
% 0.62/0.84          | ~ (l1_orders_2 @ X10)
% 0.62/0.84          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.62/0.84          | (r1_orders_2 @ X10 @ (k11_lattice3 @ X10 @ X9 @ X12) @ X9)
% 0.62/0.84          | ~ (m1_subset_1 @ (k11_lattice3 @ X10 @ X9 @ X12) @ 
% 0.62/0.84               (u1_struct_0 @ X10))
% 0.62/0.84          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['8'])).
% 0.62/0.84  thf('10', plain,
% 0.62/0.84      ((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_C)
% 0.62/0.84        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['7', '9'])).
% 0.62/0.84  thf('11', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('12', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('13', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.62/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.62/0.84  thf('14', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(fc5_yellow_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.62/0.84       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.62/0.84       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.62/0.84       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.62/0.84  thf('15', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.62/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.62/0.84  thf('16', plain,
% 0.62/0.84      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_C)
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('demod', [status(thm)], ['10', '11', '12', '13', '14', '15'])).
% 0.62/0.84  thf('17', plain,
% 0.62/0.84      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['1', '6'])).
% 0.62/0.84  thf(redefinition_r3_orders_2, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.62/0.84         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.62/0.84         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.62/0.84  thf('18', plain,
% 0.62/0.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.62/0.84          | ~ (l1_orders_2 @ X4)
% 0.62/0.84          | ~ (v3_orders_2 @ X4)
% 0.62/0.84          | (v2_struct_0 @ X4)
% 0.62/0.84          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.62/0.84          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.62/0.84          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.62/0.84      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.62/0.84  thf('19', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0)
% 0.62/0.84          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84          | ~ (v3_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.62/0.84  thf('20', plain, (![X21 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X21))),
% 0.62/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.62/0.84  thf('21', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.62/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.62/0.84  thf('22', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0)
% 0.62/0.84          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.62/0.84  thf('23', plain,
% 0.62/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_C))),
% 0.62/0.84      inference('sup-', [status(thm)], ['16', '22'])).
% 0.62/0.84  thf('24', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('25', plain,
% 0.62/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_C))),
% 0.62/0.84      inference('demod', [status(thm)], ['23', '24'])).
% 0.62/0.84  thf('26', plain,
% 0.62/0.84      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_C)
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['25'])).
% 0.62/0.84  thf('27', plain,
% 0.62/0.84      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['1', '6'])).
% 0.62/0.84  thf(t3_yellow_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.62/0.84           ( ![C:$i]:
% 0.62/0.84             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.62/0.84               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.62/0.84                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.62/0.84  thf('28', plain,
% 0.62/0.84      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ (k2_yellow_1 @ X26)))
% 0.62/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ X26) @ X25 @ X27)
% 0.62/0.84          | (r1_tarski @ X25 @ X27)
% 0.62/0.84          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ (k2_yellow_1 @ X26)))
% 0.62/0.84          | (v1_xboole_0 @ X26))),
% 0.62/0.84      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.62/0.84  thf('29', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ sk_A)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84             X0)
% 0.62/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.62/0.84  thf('30', plain,
% 0.62/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84           sk_C)
% 0.62/0.84        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84        | (v1_xboole_0 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['26', '29'])).
% 0.62/0.84  thf('31', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('32', plain,
% 0.62/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84           sk_C)
% 0.62/0.84        | (v1_xboole_0 @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['30', '31'])).
% 0.62/0.84  thf(fc6_yellow_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.62/0.84       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.62/0.84         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.62/0.84  thf('33', plain,
% 0.62/0.84      (![X24 : $i]:
% 0.62/0.84         (~ (v2_struct_0 @ (k2_yellow_1 @ X24)) | (v1_xboole_0 @ X24))),
% 0.62/0.84      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.62/0.84  thf('34', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_A)
% 0.62/0.84        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84           sk_C))),
% 0.62/0.84      inference('clc', [status(thm)], ['32', '33'])).
% 0.62/0.84  thf('35', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('36', plain,
% 0.62/0.84      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_C)),
% 0.62/0.84      inference('clc', [status(thm)], ['34', '35'])).
% 0.62/0.84  thf('37', plain,
% 0.62/0.84      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['1', '6'])).
% 0.62/0.84  thf('38', plain,
% 0.62/0.84      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.62/0.84          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.62/0.84          | ((X11) != (k11_lattice3 @ X10 @ X9 @ X12))
% 0.62/0.84          | (r1_orders_2 @ X10 @ X11 @ X12)
% 0.62/0.84          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.62/0.84          | ~ (l1_orders_2 @ X10)
% 0.62/0.84          | ~ (v2_lattice3 @ X10)
% 0.62/0.84          | ~ (v5_orders_2 @ X10)
% 0.62/0.84          | (v2_struct_0 @ X10))),
% 0.62/0.84      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.62/0.84  thf('39', plain,
% 0.62/0.84      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.62/0.84         ((v2_struct_0 @ X10)
% 0.62/0.84          | ~ (v5_orders_2 @ X10)
% 0.62/0.84          | ~ (v2_lattice3 @ X10)
% 0.62/0.84          | ~ (l1_orders_2 @ X10)
% 0.62/0.84          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.62/0.84          | (r1_orders_2 @ X10 @ (k11_lattice3 @ X10 @ X9 @ X12) @ X12)
% 0.62/0.84          | ~ (m1_subset_1 @ (k11_lattice3 @ X10 @ X9 @ X12) @ 
% 0.62/0.84               (u1_struct_0 @ X10))
% 0.62/0.84          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['38'])).
% 0.62/0.84  thf('40', plain,
% 0.62/0.84      ((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B)
% 0.62/0.84        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['37', '39'])).
% 0.62/0.84  thf('41', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('42', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('43', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.62/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.62/0.84  thf('44', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('45', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.62/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.62/0.84  thf('46', plain,
% 0.62/0.84      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B)
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.62/0.84  thf('47', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0)
% 0.62/0.84          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.62/0.84  thf('48', plain,
% 0.62/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B))),
% 0.62/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.62/0.84  thf('49', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('50', plain,
% 0.62/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B))),
% 0.62/0.84      inference('demod', [status(thm)], ['48', '49'])).
% 0.62/0.84  thf('51', plain,
% 0.62/0.84      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B)
% 0.62/0.84        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['50'])).
% 0.62/0.84  thf('52', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ sk_A)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84             X0)
% 0.62/0.84          | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.62/0.84               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.62/0.84  thf('53', plain,
% 0.62/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84           sk_B)
% 0.62/0.84        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84        | (v1_xboole_0 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.62/0.84  thf('54', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('55', plain,
% 0.62/0.84      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84           sk_B)
% 0.62/0.84        | (v1_xboole_0 @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['53', '54'])).
% 0.62/0.84  thf('56', plain,
% 0.62/0.84      (![X24 : $i]:
% 0.62/0.84         (~ (v2_struct_0 @ (k2_yellow_1 @ X24)) | (v1_xboole_0 @ X24))),
% 0.62/0.84      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.62/0.84  thf('57', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_A)
% 0.62/0.84        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84           sk_B))),
% 0.62/0.84      inference('clc', [status(thm)], ['55', '56'])).
% 0.62/0.84  thf('58', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('59', plain,
% 0.62/0.84      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B)),
% 0.62/0.84      inference('clc', [status(thm)], ['57', '58'])).
% 0.62/0.84  thf(t19_xboole_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.62/0.84       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.62/0.84  thf('60', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.62/0.84          | ~ (r1_tarski @ X0 @ X2)
% 0.62/0.84          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.62/0.84      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.62/0.84  thf('61', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84           (k3_xboole_0 @ sk_B @ X0))
% 0.62/0.84          | ~ (r1_tarski @ 
% 0.62/0.84               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.62/0.84  thf('62', plain,
% 0.62/0.84      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.62/0.84        (k3_xboole_0 @ sk_B @ sk_C))),
% 0.62/0.84      inference('sup-', [status(thm)], ['36', '61'])).
% 0.62/0.84  thf('63', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('64', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(t15_lattice3, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.84           ( ![C:$i]:
% 0.62/0.84             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.84               ( ( k11_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.62/0.84  thf('65', plain,
% 0.62/0.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.62/0.84          | ((k11_lattice3 @ X15 @ X14 @ X16)
% 0.62/0.84              = (k11_lattice3 @ X15 @ X16 @ X14))
% 0.62/0.84          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.62/0.84          | ~ (l1_orders_2 @ X15)
% 0.62/0.84          | ~ (v2_lattice3 @ X15)
% 0.62/0.84          | ~ (v5_orders_2 @ X15))),
% 0.62/0.84      inference('cnf', [status(esa)], [t15_lattice3])).
% 0.62/0.84  thf('66', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84          | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.62/0.84              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['64', '65'])).
% 0.62/0.84  thf('67', plain, (![X23 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X23))),
% 0.62/0.84      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.62/0.84  thf('68', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('69', plain, (![X19 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X19))),
% 0.62/0.84      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.62/0.84  thf('70', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.62/0.84          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 0.62/0.84              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 0.62/0.84      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.62/0.84  thf('71', plain,
% 0.62/0.84      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.62/0.84         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 0.62/0.84      inference('sup-', [status(thm)], ['63', '70'])).
% 0.62/0.84  thf('72', plain,
% 0.62/0.84      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.62/0.84        (k3_xboole_0 @ sk_B @ sk_C))),
% 0.62/0.84      inference('demod', [status(thm)], ['62', '71'])).
% 0.62/0.84  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 0.62/0.84  
% 0.62/0.84  % SZS output end Refutation
% 0.62/0.84  
% 0.62/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
