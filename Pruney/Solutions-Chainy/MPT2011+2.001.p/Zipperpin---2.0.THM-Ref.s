%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X8j5qD1BNv

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:21 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 388 expanded)
%              Number of leaves         :   26 ( 117 expanded)
%              Depth                    :   32
%              Number of atoms          : 1163 (7915 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_waybel_2_type,type,(
    k3_waybel_2: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t10_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v4_orders_2 @ C )
                & ( v7_waybel_0 @ C )
                & ( l1_waybel_0 @ C @ A ) )
             => ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) )
                & ( v4_orders_2 @ ( k3_waybel_2 @ A @ B @ C ) )
                & ( v7_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) )
                & ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v4_orders_2 @ C )
                  & ( v7_waybel_0 @ C )
                  & ( l1_waybel_0 @ C @ A ) )
               => ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) )
                  & ( v4_orders_2 @ ( k3_waybel_2 @ A @ B @ C ) )
                  & ( v7_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) )
                  & ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_waybel_9])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l16_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v4_orders_2 @ A )
      <=> ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ~ ( v4_orders_2 @ X20 )
      | ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X20 ) @ ( u1_orders_2 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l16_yellow_6])).

thf('2',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_waybel_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ~ ( v2_struct_0 @ C )
        & ( l1_waybel_0 @ C @ A ) )
     => ( ( v6_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A )
        & ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X31 )
      | ( l1_waybel_0 @ ( k3_waybel_2 @ X31 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf(d3_waybel_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( l1_waybel_0 @ C @ A ) )
             => ! [D: $i] :
                  ( ( ( v6_waybel_0 @ D @ A )
                    & ( l1_waybel_0 @ D @ A ) )
                 => ( ( D
                      = ( k3_waybel_2 @ A @ B @ C ) )
                  <=> ( ( ( g1_orders_2 @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) )
                        = ( g1_orders_2 @ ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ D ) )
                         => ? [F: $i] :
                              ( ( ( k1_funct_1 @ ( u1_waybel_0 @ A @ D ) @ E )
                                = ( k11_lattice3 @ A @ B @ F ) )
                              & ( F
                                = ( k1_funct_1 @ ( u1_waybel_0 @ A @ C ) @ E ) )
                              & ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( v6_waybel_0 @ X26 @ X25 )
      | ~ ( l1_waybel_0 @ X26 @ X25 )
      | ( X26
       != ( k3_waybel_2 @ X25 @ X24 @ X27 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X26 ) @ ( u1_orders_2 @ X26 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X27 ) @ ( u1_orders_2 @ X27 ) ) )
      | ~ ( l1_waybel_0 @ X27 @ X25 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_2])).

thf('14',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( l1_orders_2 @ X25 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X25 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ X25 @ X24 @ X27 ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ X25 @ X24 @ X27 ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X27 ) @ ( u1_orders_2 @ X27 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_waybel_2 @ X25 @ X24 @ X27 ) @ X25 )
      | ~ ( v6_waybel_0 @ ( k3_waybel_2 @ X25 @ X24 @ X27 ) @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A )
    | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) )
    | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A )
    | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X31 )
      | ( v6_waybel_0 @ ( k3_waybel_2 @ X31 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X20: $i] :
      ( ~ ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X20 ) @ ( u1_orders_2 @ X20 ) ) )
      | ( v4_orders_2 @ X20 )
      | ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l16_yellow_6])).

thf('37',plain,
    ( ~ ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( l1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_waybel_0 @ X3 @ X4 )
      | ( l1_orders_2 @ X3 )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('40',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('42',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('49',plain,
    ( ~ ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A )
   <= ~ ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('50',plain,(
    l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc5_waybel_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ~ ( v2_struct_0 @ C )
        & ( l1_waybel_0 @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ) )).

thf('53',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_waybel_0 @ X35 @ X34 )
      | ~ ( v2_struct_0 @ ( k3_waybel_2 @ X34 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_waybel_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A ) )
   <= ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(l15_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v7_waybel_0 @ A )
      <=> ( v7_waybel_0 @ ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X19: $i] :
      ( ~ ( v7_waybel_0 @ X19 )
      | ( v7_waybel_0 @ ( g1_orders_2 @ ( u1_struct_0 @ X19 ) @ ( u1_orders_2 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l15_yellow_6])).

thf('65',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('66',plain,(
    ! [X19: $i] :
      ( ~ ( v7_waybel_0 @ ( g1_orders_2 @ ( u1_struct_0 @ X19 ) @ ( u1_orders_2 @ X19 ) ) )
      | ( v7_waybel_0 @ X19 )
      | ~ ( l1_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l15_yellow_6])).

thf('67',plain,
    ( ~ ( v7_waybel_0 @ ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( l1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('69',plain,
    ( ~ ( v7_waybel_0 @ ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_orders_2 @ sk_C_1 )
    | ~ ( v7_waybel_0 @ sk_C_1 )
    | ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_waybel_0 @ X3 @ X4 )
      | ( l1_orders_2 @ X3 )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('73',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('75',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v7_waybel_0 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['70','75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('81',plain,
    ( ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ~ ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('89',plain,(
    v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('91',plain,(
    ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['50','63','89','90'])).

thf('92',plain,(
    ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['47','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_orders_2 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['45','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_orders_2 @ sk_C_1 )
    | ~ ( v4_orders_2 @ sk_C_1 )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','93'])).

thf('95',plain,(
    l1_orders_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['73','74'])).

thf('96',plain,(
    v4_orders_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X8j5qD1BNv
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 235 iterations in 0.203s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.65  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.46/0.65  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.65  thf(k3_waybel_2_type, type, k3_waybel_2: $i > $i > $i > $i).
% 0.46/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.65  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.46/0.65  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.46/0.65  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.46/0.65  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.65  thf(t10_waybel_9, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.46/0.65                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.46/0.65               ( ( ~( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) ) ) & 
% 0.46/0.65                 ( v4_orders_2 @ ( k3_waybel_2 @ A @ B @ C ) ) & 
% 0.46/0.65                 ( v7_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) ) & 
% 0.46/0.65                 ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65              ( ![C:$i]:
% 0.46/0.65                ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.46/0.65                    ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.46/0.65                  ( ( ~( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) ) ) & 
% 0.46/0.65                    ( v4_orders_2 @ ( k3_waybel_2 @ A @ B @ C ) ) & 
% 0.46/0.65                    ( v7_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) ) & 
% 0.46/0.65                    ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t10_waybel_9])).
% 0.46/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(l16_yellow_6, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.65       ( ( v4_orders_2 @ A ) <=>
% 0.46/0.65         ( v4_orders_2 @
% 0.46/0.65           ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X20 : $i]:
% 0.46/0.65         (~ (v4_orders_2 @ X20)
% 0.46/0.65          | (v4_orders_2 @ 
% 0.46/0.65             (g1_orders_2 @ (u1_struct_0 @ X20) @ (u1_orders_2 @ X20)))
% 0.46/0.65          | ~ (l1_orders_2 @ X20)
% 0.46/0.65          | (v2_struct_0 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [l16_yellow_6])).
% 0.46/0.65  thf('2', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_k3_waybel_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.65         ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.46/0.65       ( ( v6_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) & 
% 0.46/0.65         ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.46/0.65          | ~ (l1_orders_2 @ X31)
% 0.46/0.65          | (v2_struct_0 @ X31)
% 0.46/0.65          | (v2_struct_0 @ X32)
% 0.46/0.65          | ~ (l1_waybel_0 @ X32 @ X31)
% 0.46/0.65          | (l1_waybel_0 @ (k3_waybel_2 @ X31 @ X30 @ X32) @ X31))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k3_waybel_2])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (l1_orders_2 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_C_1)
% 0.46/0.65        | (l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '7'])).
% 0.46/0.65  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_C_1))),
% 0.46/0.65      inference('clc', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf('11', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.46/0.65      inference('clc', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf(d3_waybel_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.46/0.65               ( ![D:$i]:
% 0.46/0.65                 ( ( ( v6_waybel_0 @ D @ A ) & ( l1_waybel_0 @ D @ A ) ) =>
% 0.46/0.65                   ( ( ( D ) = ( k3_waybel_2 @ A @ B @ C ) ) <=>
% 0.46/0.65                     ( ( ( g1_orders_2 @
% 0.46/0.65                           ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) =
% 0.46/0.65                         ( g1_orders_2 @
% 0.46/0.65                           ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) & 
% 0.46/0.65                       ( ![E:$i]:
% 0.46/0.65                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ D ) ) =>
% 0.46/0.65                           ( ?[F:$i]:
% 0.46/0.65                             ( ( ( k1_funct_1 @ ( u1_waybel_0 @ A @ D ) @ E ) =
% 0.46/0.65                                 ( k11_lattice3 @ A @ B @ F ) ) & 
% 0.46/0.65                               ( ( F ) =
% 0.46/0.65                                 ( k1_funct_1 @ ( u1_waybel_0 @ A @ C ) @ E ) ) & 
% 0.46/0.65                               ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.46/0.65          | ~ (v6_waybel_0 @ X26 @ X25)
% 0.46/0.65          | ~ (l1_waybel_0 @ X26 @ X25)
% 0.46/0.65          | ((X26) != (k3_waybel_2 @ X25 @ X24 @ X27))
% 0.46/0.65          | ((g1_orders_2 @ (u1_struct_0 @ X26) @ (u1_orders_2 @ X26))
% 0.46/0.65              = (g1_orders_2 @ (u1_struct_0 @ X27) @ (u1_orders_2 @ X27)))
% 0.46/0.65          | ~ (l1_waybel_0 @ X27 @ X25)
% 0.46/0.65          | (v2_struct_0 @ X27)
% 0.46/0.65          | ~ (l1_orders_2 @ X25)
% 0.46/0.65          | (v2_struct_0 @ X25))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_waybel_2])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X27 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X25)
% 0.46/0.65          | ~ (l1_orders_2 @ X25)
% 0.46/0.65          | (v2_struct_0 @ X27)
% 0.46/0.65          | ~ (l1_waybel_0 @ X27 @ X25)
% 0.46/0.65          | ((g1_orders_2 @ (u1_struct_0 @ (k3_waybel_2 @ X25 @ X24 @ X27)) @ 
% 0.46/0.65              (u1_orders_2 @ (k3_waybel_2 @ X25 @ X24 @ X27)))
% 0.46/0.65              = (g1_orders_2 @ (u1_struct_0 @ X27) @ (u1_orders_2 @ X27)))
% 0.46/0.65          | ~ (l1_waybel_0 @ (k3_waybel_2 @ X25 @ X24 @ X27) @ X25)
% 0.46/0.65          | ~ (v6_waybel_0 @ (k3_waybel_2 @ X25 @ X24 @ X27) @ X25)
% 0.46/0.65          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)
% 0.46/0.65        | ((g1_orders_2 @ 
% 0.46/0.65            (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.46/0.65            (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65            = (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))
% 0.46/0.65        | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_C_1)
% 0.46/0.65        | ~ (l1_orders_2 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['12', '14'])).
% 0.46/0.65  thf('16', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('17', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      ((~ (v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)
% 0.46/0.65        | ((g1_orders_2 @ 
% 0.46/0.65            (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.46/0.65            (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65            = (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))
% 0.46/0.65        | (v2_struct_0 @ sk_C_1)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.46/0.65  thf('20', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('21', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.46/0.65          | ~ (l1_orders_2 @ X31)
% 0.46/0.65          | (v2_struct_0 @ X31)
% 0.46/0.65          | (v2_struct_0 @ X32)
% 0.46/0.65          | ~ (l1_waybel_0 @ X32 @ X31)
% 0.46/0.65          | (v6_waybel_0 @ (k3_waybel_2 @ X31 @ X30 @ X32) @ X31))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k3_waybel_2])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (l1_orders_2 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ X0) @ sk_A)
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_C_1)
% 0.46/0.65        | (v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['20', '25'])).
% 0.46/0.65  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_C_1))),
% 0.46/0.65      inference('clc', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      ((v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.46/0.65      inference('clc', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      ((((g1_orders_2 @ 
% 0.46/0.65          (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.46/0.65          (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65          = (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))
% 0.46/0.65        | (v2_struct_0 @ sk_C_1)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['19', '30'])).
% 0.46/0.65  thf('32', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | ((g1_orders_2 @ 
% 0.46/0.65            (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.46/0.65            (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65            = (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1))))),
% 0.46/0.65      inference('clc', [status(thm)], ['31', '32'])).
% 0.46/0.65  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (((g1_orders_2 @ 
% 0.46/0.65         (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.46/0.65         (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65         = (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))),
% 0.46/0.65      inference('clc', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X20 : $i]:
% 0.46/0.65         (~ (v4_orders_2 @ 
% 0.46/0.65             (g1_orders_2 @ (u1_struct_0 @ X20) @ (u1_orders_2 @ X20)))
% 0.46/0.65          | (v4_orders_2 @ X20)
% 0.46/0.65          | ~ (l1_orders_2 @ X20)
% 0.46/0.65          | (v2_struct_0 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [l16_yellow_6])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      ((~ (v4_orders_2 @ 
% 0.46/0.65           (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))
% 0.46/0.65        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | ~ (l1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.46/0.65      inference('clc', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf(dt_l1_waybel_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_struct_0 @ A ) =>
% 0.46/0.65       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (l1_waybel_0 @ X3 @ X4) | (l1_orders_2 @ X3) | ~ (l1_struct_0 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (l1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.65  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_l1_orders_2, axiom,
% 0.46/0.65    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.65  thf('42', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_orders_2 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.46/0.65  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('44', plain, ((l1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['40', '43'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      ((~ (v4_orders_2 @ 
% 0.46/0.65           (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))
% 0.46/0.65        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['37', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | ~ (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | ~ (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | ~ (l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      ((~ (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65         <= (~ ((v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.46/0.65      inference('split', [status(esa)], ['46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.46/0.65      inference('clc', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      ((~ (l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A))
% 0.46/0.65         <= (~ ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A)))),
% 0.46/0.65      inference('split', [status(esa)], ['46'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65         <= (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.46/0.65      inference('split', [status(esa)], ['46'])).
% 0.46/0.65  thf('52', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(fc5_waybel_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.65         ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.46/0.65       ( ( ~( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) ) ) & 
% 0.46/0.65         ( v6_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ))).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 0.46/0.65          | ~ (l1_orders_2 @ X34)
% 0.46/0.65          | (v2_struct_0 @ X34)
% 0.46/0.65          | (v2_struct_0 @ X35)
% 0.46/0.65          | ~ (l1_waybel_0 @ X35 @ X34)
% 0.46/0.65          | ~ (v2_struct_0 @ (k3_waybel_2 @ X34 @ X33 @ X35)))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc5_waybel_2])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (l1_orders_2 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      ((((v2_struct_0 @ sk_A)
% 0.46/0.65         | (v2_struct_0 @ sk_C_1)
% 0.46/0.65         | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)))
% 0.46/0.65         <= (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '56'])).
% 0.46/0.65  thf('58', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1)))
% 0.46/0.65         <= (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.46/0.65      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_C_1))
% 0.46/0.65         <= (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.46/0.65      inference('clc', [status(thm)], ['59', '60'])).
% 0.46/0.65  thf('62', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (~ ((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf(l15_yellow_6, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.65       ( ( v7_waybel_0 @ A ) <=>
% 0.46/0.65         ( v7_waybel_0 @
% 0.46/0.65           ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X19 : $i]:
% 0.46/0.65         (~ (v7_waybel_0 @ X19)
% 0.46/0.65          | (v7_waybel_0 @ 
% 0.46/0.65             (g1_orders_2 @ (u1_struct_0 @ X19) @ (u1_orders_2 @ X19)))
% 0.46/0.65          | ~ (l1_orders_2 @ X19)
% 0.46/0.65          | (v2_struct_0 @ X19))),
% 0.46/0.65      inference('cnf', [status(esa)], [l15_yellow_6])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (((g1_orders_2 @ 
% 0.46/0.65         (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.46/0.65         (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65         = (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))),
% 0.46/0.65      inference('clc', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X19 : $i]:
% 0.46/0.65         (~ (v7_waybel_0 @ 
% 0.46/0.65             (g1_orders_2 @ (u1_struct_0 @ X19) @ (u1_orders_2 @ X19)))
% 0.46/0.65          | (v7_waybel_0 @ X19)
% 0.46/0.65          | ~ (l1_orders_2 @ X19)
% 0.46/0.65          | (v2_struct_0 @ X19))),
% 0.46/0.65      inference('cnf', [status(esa)], [l15_yellow_6])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      ((~ (v7_waybel_0 @ 
% 0.46/0.65           (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))
% 0.46/0.65        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | ~ (l1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.65  thf('68', plain, ((l1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['40', '43'])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      ((~ (v7_waybel_0 @ 
% 0.46/0.65           (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1)))
% 0.46/0.65        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_C_1)
% 0.46/0.65        | ~ (l1_orders_2 @ sk_C_1)
% 0.46/0.65        | ~ (v7_waybel_0 @ sk_C_1)
% 0.46/0.65        | (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['64', '69'])).
% 0.46/0.65  thf('71', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (l1_waybel_0 @ X3 @ X4) | (l1_orders_2 @ X3) | ~ (l1_struct_0 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.46/0.65  thf('73', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.65  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('75', plain, ((l1_orders_2 @ sk_C_1)),
% 0.46/0.65      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.65  thf('76', plain, ((v7_waybel_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('77', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_C_1)
% 0.46/0.65        | (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['70', '75', '76'])).
% 0.46/0.65  thf('78', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('clc', [status(thm)], ['77', '78'])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      (((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_C_1)
% 0.46/0.65        | ~ (l1_waybel_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf('82', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.65  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('85', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_C_1)
% 0.46/0.65        | (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('clc', [status(thm)], ['83', '84'])).
% 0.46/0.65  thf('86', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('87', plain, ((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.46/0.65      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      ((~ (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.46/0.65         <= (~ ((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.46/0.65      inference('split', [status(esa)], ['46'])).
% 0.46/0.65  thf('89', plain, (((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      (~ ((v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))) | 
% 0.46/0.65       ~ ((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))) | 
% 0.46/0.65       ((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))) | 
% 0.46/0.65       ~ ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.46/0.65      inference('split', [status(esa)], ['46'])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      (~ ((v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['50', '63', '89', '90'])).
% 0.46/0.65  thf('92', plain, (~ (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['47', '91'])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.46/0.65        | ~ (v4_orders_2 @ 
% 0.46/0.65             (g1_orders_2 @ (u1_struct_0 @ sk_C_1) @ (u1_orders_2 @ sk_C_1))))),
% 0.46/0.65      inference('clc', [status(thm)], ['45', '92'])).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_C_1)
% 0.46/0.65        | ~ (l1_orders_2 @ sk_C_1)
% 0.46/0.65        | ~ (v4_orders_2 @ sk_C_1)
% 0.46/0.65        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '93'])).
% 0.46/0.65  thf('95', plain, ((l1_orders_2 @ sk_C_1)),
% 0.46/0.65      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.65  thf('96', plain, ((v4_orders_2 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('97', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_C_1)
% 0.46/0.65        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.46/0.65  thf('98', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('99', plain, ((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.46/0.65      inference('clc', [status(thm)], ['97', '98'])).
% 0.46/0.65  thf('100', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B_1 @ X0))
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('101', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_C_1)
% 0.46/0.65        | ~ (l1_waybel_0 @ sk_C_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.65  thf('102', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('103', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['101', '102'])).
% 0.46/0.65  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('105', plain, ((v2_struct_0 @ sk_C_1)),
% 0.46/0.65      inference('clc', [status(thm)], ['103', '104'])).
% 0.46/0.65  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
