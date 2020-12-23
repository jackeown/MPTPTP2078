%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ELJs8T2KnI

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:07 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 197 expanded)
%              Number of leaves         :   31 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          : 1289 (3078 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t3_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( r3_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) )
            & ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( r3_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) )
              & ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_waybel_7])).

thf('0',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ~ ( v1_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('2',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(t32_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( B
                = ( k1_yellow_0 @ A @ C ) )
            <=> ( ( r2_lattice3 @ A @ C @ B )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ C @ D )
                     => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( X15
       != ( k1_yellow_0 @ X16 @ X17 ) )
      | ( r2_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v3_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t32_yellow_0])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v3_lattice3 @ X16 )
      | ~ ( l1_orders_2 @ X16 )
      | ( r2_lattice3 @ X16 @ X17 @ ( k1_yellow_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(t9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ C @ D )
                 => ( r1_lattice3 @ A @ B @ D ) )
                & ( ( r2_lattice3 @ A @ C @ D )
                 => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r2_lattice3 @ X27 @ X26 @ X28 )
      | ( r2_lattice3 @ X27 @ X25 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_lattice3 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X2 @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ( r2_lattice3 @ X1 @ X2 @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v3_lattice3 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_lattice3 @ X0 @ sk_B @ ( k1_yellow_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( X15
       != ( k1_yellow_0 @ X16 @ X17 ) )
      | ~ ( r2_lattice3 @ X16 @ X17 @ X18 )
      | ( r1_orders_2 @ X16 @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v3_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t32_yellow_0])).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v3_lattice3 @ X16 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( r1_orders_2 @ X16 @ ( k1_yellow_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r2_lattice3 @ X16 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ sk_B ) @ ( k1_yellow_0 @ X0 @ sk_C ) )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ sk_B ) @ ( k1_yellow_0 @ X0 @ sk_C ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ sk_B ) @ ( k1_yellow_0 @ X0 @ sk_C ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ sk_B ) @ ( k1_yellow_0 @ X0 @ sk_C ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
   <= ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r2_yellow_0 @ A @ B )
          & ( r1_yellow_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_yellow_0 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(d10_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_yellow_0 @ A @ B )
           => ( ( C
                = ( k2_yellow_0 @ A @ B ) )
            <=> ( ( r1_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X6
       != ( k2_yellow_0 @ X4 @ X5 ) )
      | ( r1_lattice3 @ X4 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ( r1_lattice3 @ X4 @ X5 @ ( k2_yellow_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('57',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_lattice3 @ X27 @ X26 @ X28 )
      | ( r1_lattice3 @ X27 @ X25 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_yellow_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X1 @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['39','62'])).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('66',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
       != ( k2_yellow_0 @ X4 @ X5 ) )
      | ~ ( r1_lattice3 @ X4 @ X5 @ X7 )
      | ( r1_orders_2 @ X4 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('67',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r2_yellow_0 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X7 @ ( k2_yellow_0 @ X4 @ X5 ) )
      | ~ ( r1_lattice3 @ X4 @ X5 @ X7 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r2_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('75',plain,(
    r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['37'])).

thf('77',plain,(
    r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['37'])).

thf('79',plain,(
    ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_B ) @ ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['38','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','80'])).

thf('82',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['4','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ELJs8T2KnI
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 98 iterations in 0.082s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.36/0.55  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.36/0.55  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.36/0.55  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.36/0.55  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.36/0.55  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.36/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.36/0.55  thf(v3_lattice3_type, type, v3_lattice3: $i > $o).
% 0.36/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.36/0.55  thf(t3_waybel_7, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.36/0.55         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.36/0.55         ( l1_orders_2 @ A ) ) =>
% 0.36/0.55       ( ![B:$i,C:$i]:
% 0.36/0.55         ( ( r1_tarski @ B @ C ) =>
% 0.36/0.55           ( ( r3_orders_2 @
% 0.36/0.55               A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.36/0.55             ( r1_orders_2 @
% 0.36/0.55               A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.36/0.55            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( v3_lattice3 @ A ) & 
% 0.36/0.55            ( l1_orders_2 @ A ) ) =>
% 0.36/0.55          ( ![B:$i,C:$i]:
% 0.36/0.55            ( ( r1_tarski @ B @ C ) =>
% 0.36/0.55              ( ( r3_orders_2 @
% 0.36/0.55                  A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) & 
% 0.36/0.55                ( r1_orders_2 @
% 0.36/0.55                  A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t3_waybel_7])).
% 0.36/0.55  thf('0', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc1_lattice3, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X3 : $i]:
% 0.36/0.55         (~ (v1_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.36/0.55  thf('2', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf('3', plain, ((v1_lattice3 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('4', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k1_yellow_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X8)
% 0.36/0.55          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.36/0.55  thf(t32_yellow_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.36/0.55         ( v3_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) <=>
% 0.36/0.55               ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.36/0.55                 ( ![D:$i]:
% 0.36/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                     ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.36/0.55                       ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.36/0.55          | ((X15) != (k1_yellow_0 @ X16 @ X17))
% 0.36/0.55          | (r2_lattice3 @ X16 @ X17 @ X15)
% 0.36/0.55          | ~ (l1_orders_2 @ X16)
% 0.36/0.55          | ~ (v3_lattice3 @ X16)
% 0.36/0.55          | ~ (v5_orders_2 @ X16)
% 0.36/0.55          | (v2_struct_0 @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t32_yellow_0])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X16)
% 0.36/0.55          | ~ (v5_orders_2 @ X16)
% 0.36/0.55          | ~ (v3_lattice3 @ X16)
% 0.36/0.55          | ~ (l1_orders_2 @ X16)
% 0.36/0.55          | (r2_lattice3 @ X16 @ X17 @ (k1_yellow_0 @ X16 @ X17))
% 0.36/0.55          | ~ (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X8)
% 0.36/0.55          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.36/0.55  thf(t9_yellow_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( ![B:$i,C:$i]:
% 0.36/0.55         ( ( r1_tarski @ B @ C ) =>
% 0.36/0.55           ( ![D:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.36/0.55                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X25 @ X26)
% 0.36/0.55          | ~ (r2_lattice3 @ X27 @ X26 @ X28)
% 0.36/0.55          | (r2_lattice3 @ X27 @ X25 @ X28)
% 0.36/0.55          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.36/0.55          | ~ (l1_orders_2 @ X27))),
% 0.36/0.55      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (r1_tarski @ X2 @ X3))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X2 @ X3)
% 0.36/0.55          | ~ (r2_lattice3 @ X0 @ X3 @ (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X1)
% 0.36/0.55          | ~ (v3_lattice3 @ X1)
% 0.36/0.55          | ~ (v5_orders_2 @ X1)
% 0.36/0.55          | (v2_struct_0 @ X1)
% 0.36/0.55          | ~ (l1_orders_2 @ X1)
% 0.36/0.55          | (r2_lattice3 @ X1 @ X2 @ (k1_yellow_0 @ X1 @ X0))
% 0.36/0.55          | ~ (r1_tarski @ X2 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X2 @ X0)
% 0.36/0.55          | (r2_lattice3 @ X1 @ X2 @ (k1_yellow_0 @ X1 @ X0))
% 0.36/0.55          | (v2_struct_0 @ X1)
% 0.36/0.55          | ~ (v5_orders_2 @ X1)
% 0.36/0.55          | ~ (v3_lattice3 @ X1)
% 0.36/0.55          | ~ (l1_orders_2 @ X1))),
% 0.36/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | (r2_lattice3 @ X0 @ sk_B @ (k1_yellow_0 @ X0 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X8)
% 0.36/0.55          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X8)
% 0.36/0.55          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.36/0.55          | ((X15) != (k1_yellow_0 @ X16 @ X17))
% 0.36/0.55          | ~ (r2_lattice3 @ X16 @ X17 @ X18)
% 0.36/0.55          | (r1_orders_2 @ X16 @ X15 @ X18)
% 0.36/0.55          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.36/0.55          | ~ (l1_orders_2 @ X16)
% 0.36/0.55          | ~ (v3_lattice3 @ X16)
% 0.36/0.55          | ~ (v5_orders_2 @ X16)
% 0.36/0.55          | (v2_struct_0 @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t32_yellow_0])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X16)
% 0.36/0.55          | ~ (v5_orders_2 @ X16)
% 0.36/0.55          | ~ (v3_lattice3 @ X16)
% 0.36/0.55          | ~ (l1_orders_2 @ X16)
% 0.36/0.55          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.36/0.55          | (r1_orders_2 @ X16 @ (k1_yellow_0 @ X16 @ X17) @ X18)
% 0.36/0.55          | ~ (r2_lattice3 @ X16 @ X17 @ X18)
% 0.36/0.55          | ~ (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.36/0.55          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '21'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.36/0.55          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.36/0.55             (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.36/0.55             (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ sk_B) @ 
% 0.36/0.55             (k1_yellow_0 @ X0 @ sk_C))
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ sk_B) @ 
% 0.36/0.55           (k1_yellow_0 @ X0 @ sk_C))
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X8)
% 0.36/0.55          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X8)
% 0.36/0.55          | (m1_subset_1 @ (k1_yellow_0 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.36/0.55  thf(redefinition_r3_orders_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.36/0.55         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X1)
% 0.36/0.55          | ~ (v3_orders_2 @ X1)
% 0.36/0.55          | (v2_struct_0 @ X1)
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.36/0.55          | (r3_orders_2 @ X1 @ X0 @ X2)
% 0.36/0.55          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.36/0.55          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v3_orders_2 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (v3_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.36/0.55          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.36/0.55               (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.36/0.55             (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v3_orders_2 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (v3_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.36/0.55             (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.36/0.55               (k1_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ sk_B) @ 
% 0.36/0.55             (k1_yellow_0 @ X0 @ sk_C))
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v3_orders_2 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['27', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v3_orders_2 @ X0)
% 0.36/0.55          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ sk_B) @ 
% 0.36/0.55             (k1_yellow_0 @ X0 @ sk_C))
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (v3_lattice3 @ X0)
% 0.36/0.55          | ~ (v5_orders_2 @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.36/0.55           (k1_yellow_0 @ sk_A @ sk_C))
% 0.36/0.55        | ~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.36/0.55             (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      ((~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.36/0.55           (k1_yellow_0 @ sk_A @ sk_C)))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.36/0.55               (k1_yellow_0 @ sk_A @ sk_C))))),
% 0.36/0.55      inference('split', [status(esa)], ['37'])).
% 0.36/0.55  thf('39', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t17_yellow_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.36/0.55         ( v3_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]: ( ( r2_yellow_0 @ A @ B ) & ( r1_yellow_0 @ A @ B ) ) ) ))).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         ((r2_yellow_0 @ X12 @ X13)
% 0.36/0.55          | ~ (l1_orders_2 @ X12)
% 0.36/0.55          | ~ (v3_lattice3 @ X12)
% 0.36/0.55          | ~ (v5_orders_2 @ X12)
% 0.36/0.55          | (v2_struct_0 @ X12))),
% 0.36/0.55      inference('cnf', [status(esa)], [t17_yellow_0])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_A)
% 0.36/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.36/0.55          | ~ (v3_lattice3 @ sk_A)
% 0.36/0.55          | (r2_yellow_0 @ sk_A @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('44', plain, ((v3_lattice3 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      (![X0 : $i]: ((v2_struct_0 @ sk_A) | (r2_yellow_0 @ sk_A @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.36/0.55  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('47', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.36/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.36/0.55  thf(dt_k2_yellow_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X10)
% 0.36/0.55          | (m1_subset_1 @ (k2_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.36/0.55  thf(d10_yellow_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( ![B:$i,C:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55           ( ( r2_yellow_0 @ A @ B ) =>
% 0.36/0.55             ( ( ( C ) = ( k2_yellow_0 @ A @ B ) ) <=>
% 0.36/0.55               ( ( r1_lattice3 @ A @ B @ C ) & 
% 0.36/0.55                 ( ![D:$i]:
% 0.36/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                     ( ( r1_lattice3 @ A @ B @ D ) =>
% 0.36/0.55                       ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (((X6) != (k2_yellow_0 @ X4 @ X5))
% 0.36/0.55          | (r1_lattice3 @ X4 @ X5 @ X6)
% 0.36/0.55          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.36/0.55          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.36/0.55          | ~ (l1_orders_2 @ X4))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X4)
% 0.36/0.55          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.36/0.55          | ~ (m1_subset_1 @ (k2_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.36/0.55          | (r1_lattice3 @ X4 @ X5 @ (k2_yellow_0 @ X4 @ X5)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['49'])).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['48', '50'])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_yellow_0 @ X0 @ X1)
% 0.36/0.55          | (r1_lattice3 @ X0 @ X1 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ sk_A)
% 0.36/0.55          | (r1_lattice3 @ sk_A @ X0 @ (k2_yellow_0 @ sk_A @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['47', '52'])).
% 0.36/0.55  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      (![X0 : $i]: (r1_lattice3 @ sk_A @ X0 @ (k2_yellow_0 @ sk_A @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X10)
% 0.36/0.55          | (m1_subset_1 @ (k2_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X25 @ X26)
% 0.36/0.55          | ~ (r1_lattice3 @ X27 @ X26 @ X28)
% 0.36/0.55          | (r1_lattice3 @ X27 @ X25 @ X28)
% 0.36/0.55          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.36/0.55          | ~ (l1_orders_2 @ X27))),
% 0.36/0.55      inference('cnf', [status(esa)], [t9_yellow_0])).
% 0.36/0.55  thf('58', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (r1_lattice3 @ X0 @ X3 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (r1_tarski @ X2 @ X3))),
% 0.36/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X2 @ X3)
% 0.36/0.55          | ~ (r1_lattice3 @ X0 @ X3 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['58'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ sk_A)
% 0.36/0.55          | (r1_lattice3 @ sk_A @ X1 @ (k2_yellow_0 @ sk_A @ X0))
% 0.36/0.55          | ~ (r1_tarski @ X1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['55', '59'])).
% 0.36/0.55  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('62', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r1_lattice3 @ sk_A @ X1 @ (k2_yellow_0 @ sk_A @ X0))
% 0.36/0.55          | ~ (r1_tarski @ X1 @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.55  thf('63', plain, ((r1_lattice3 @ sk_A @ sk_B @ (k2_yellow_0 @ sk_A @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '62'])).
% 0.36/0.55  thf('64', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X10)
% 0.36/0.55          | (m1_subset_1 @ (k2_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.36/0.55  thf('65', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X10)
% 0.36/0.55          | (m1_subset_1 @ (k2_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_0])).
% 0.36/0.55  thf('66', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.55         (((X6) != (k2_yellow_0 @ X4 @ X5))
% 0.36/0.55          | ~ (r1_lattice3 @ X4 @ X5 @ X7)
% 0.36/0.55          | (r1_orders_2 @ X4 @ X7 @ X6)
% 0.36/0.55          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.36/0.55          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.36/0.55          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.36/0.55          | ~ (l1_orders_2 @ X4))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_yellow_0])).
% 0.36/0.55  thf('67', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X4)
% 0.36/0.55          | ~ (r2_yellow_0 @ X4 @ X5)
% 0.36/0.55          | ~ (m1_subset_1 @ (k2_yellow_0 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.36/0.55          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.36/0.55          | (r1_orders_2 @ X4 @ X7 @ (k2_yellow_0 @ X4 @ X5))
% 0.36/0.55          | ~ (r1_lattice3 @ X4 @ X5 @ X7))),
% 0.36/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.55  thf('68', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.36/0.55          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (r2_yellow_0 @ X0 @ X1)
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['65', '67'])).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r2_yellow_0 @ X0 @ X1)
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | (r1_orders_2 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (r1_lattice3 @ X0 @ X1 @ X2)
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['68'])).
% 0.36/0.55  thf('70', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (l1_orders_2 @ X0)
% 0.36/0.55          | ~ (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | (r1_orders_2 @ X0 @ (k2_yellow_0 @ X0 @ X1) @ 
% 0.36/0.55             (k2_yellow_0 @ X0 @ X2))
% 0.36/0.55          | ~ (r2_yellow_0 @ X0 @ X2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['64', '69'])).
% 0.36/0.55  thf('71', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r2_yellow_0 @ X0 @ X2)
% 0.36/0.55          | (r1_orders_2 @ X0 @ (k2_yellow_0 @ X0 @ X1) @ 
% 0.36/0.55             (k2_yellow_0 @ X0 @ X2))
% 0.36/0.55          | ~ (r1_lattice3 @ X0 @ X2 @ (k2_yellow_0 @ X0 @ X1))
% 0.36/0.55          | ~ (l1_orders_2 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['70'])).
% 0.36/0.55  thf('72', plain,
% 0.36/0.55      ((~ (l1_orders_2 @ sk_A)
% 0.36/0.55        | (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.36/0.55           (k2_yellow_0 @ sk_A @ sk_B))
% 0.36/0.55        | ~ (r2_yellow_0 @ sk_A @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['63', '71'])).
% 0.36/0.55  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('74', plain, (![X0 : $i]: (r2_yellow_0 @ sk_A @ X0)),
% 0.36/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.36/0.55  thf('75', plain,
% 0.36/0.55      ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.36/0.55        (k2_yellow_0 @ sk_A @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.36/0.55  thf('76', plain,
% 0.36/0.55      ((~ (r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.36/0.55           (k2_yellow_0 @ sk_A @ sk_B)))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.36/0.55               (k2_yellow_0 @ sk_A @ sk_B))))),
% 0.36/0.55      inference('split', [status(esa)], ['37'])).
% 0.36/0.55  thf('77', plain,
% 0.36/0.55      (((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.36/0.55         (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.55  thf('78', plain,
% 0.36/0.55      (~
% 0.36/0.55       ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.36/0.55         (k1_yellow_0 @ sk_A @ sk_C))) | 
% 0.36/0.55       ~
% 0.36/0.55       ((r1_orders_2 @ sk_A @ (k2_yellow_0 @ sk_A @ sk_C) @ 
% 0.36/0.55         (k2_yellow_0 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('split', [status(esa)], ['37'])).
% 0.36/0.55  thf('79', plain,
% 0.36/0.55      (~
% 0.36/0.55       ((r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.36/0.55         (k1_yellow_0 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.36/0.55  thf('80', plain,
% 0.36/0.55      (~ (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ sk_B) @ 
% 0.36/0.55          (k1_yellow_0 @ sk_A @ sk_C))),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['38', '79'])).
% 0.36/0.55  thf('81', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.36/0.55        | ~ (v3_lattice3 @ sk_A)
% 0.36/0.55        | ~ (l1_orders_2 @ sk_A)
% 0.36/0.55        | ~ (v3_orders_2 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['36', '80'])).
% 0.36/0.55  thf('82', plain, ((v5_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('83', plain, ((v3_lattice3 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('85', plain, ((v3_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('86', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.36/0.55  thf('87', plain, ($false), inference('demod', [status(thm)], ['4', '86'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
