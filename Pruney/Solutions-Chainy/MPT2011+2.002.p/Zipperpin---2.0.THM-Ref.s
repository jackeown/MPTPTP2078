%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KNGmAjNaVq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 263 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   21
%              Number of atoms          : 1068 (5274 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k3_waybel_2_type,type,(
    k3_waybel_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l16_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v4_orders_2 @ A )
      <=> ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ~ ( v4_orders_2 @ X3 )
      | ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X3 ) @ ( u1_orders_2 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l16_yellow_6])).

thf('2',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ( l1_waybel_0 @ ( k3_waybel_2 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) @ sk_A )
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
      ( ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v6_waybel_0 @ X6 @ X5 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( X6
       != ( k3_waybel_2 @ X5 @ X4 @ X7 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X6 ) @ ( u1_orders_2 @ X6 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) ) )
      | ~ ( l1_waybel_0 @ X7 @ X5 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_2])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X5 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ X5 @ X4 @ X7 ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ X5 @ X4 @ X7 ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_waybel_2 @ X5 @ X4 @ X7 ) @ X5 )
      | ~ ( v6_waybel_0 @ ( k3_waybel_2 @ X5 @ X4 @ X7 ) @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ( v6_waybel_0 @ ( k3_waybel_2 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v6_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i] :
      ( ~ ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X3 ) @ ( u1_orders_2 @ X3 ) ) )
      | ( v4_orders_2 @ X3 )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l16_yellow_6])).

thf('36',plain,
    ( ~ ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ X1 @ X2 )
      | ( l1_orders_2 @ X1 )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('39',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ~ ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_waybel_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ~ ( v2_struct_0 @ C )
        & ( v7_waybel_0 @ C )
        & ( l1_waybel_0 @ C @ A ) )
     => ( ( v6_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A )
        & ( v7_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ( v7_waybel_0 @ ( k3_waybel_2 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_waybel_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v7_waybel_0 @ sk_C )
    | ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['45'])).

thf('61',plain,(
    v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['45'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ~ ( v2_struct_0 @ ( k3_waybel_2 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_waybel_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A ) )
   <= ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('76',plain,
    ( ~ ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A )
   <= ~ ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('77',plain,(
    l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v7_waybel_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['45'])).

thf('79',plain,(
    ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['61','74','77','78'])).

thf('80',plain,(
    ~ ( v4_orders_2 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['46','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v4_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['44','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( l1_orders_2 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','81'])).

thf('83',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ X1 @ X2 )
      | ( l1_orders_2 @ X1 )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('85',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('87',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_waybel_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KNGmAjNaVq
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 50 iterations in 0.039s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.50  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.50  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.20/0.50  thf(k3_waybel_2_type, type, k3_waybel_2: $i > $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.50  thf(t10_waybel_9, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.20/0.50                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.20/0.50               ( ( ~( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) ) ) & 
% 0.20/0.50                 ( v4_orders_2 @ ( k3_waybel_2 @ A @ B @ C ) ) & 
% 0.20/0.50                 ( v7_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) ) & 
% 0.20/0.50                 ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.20/0.50                    ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.20/0.50                  ( ( ~( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) ) ) & 
% 0.20/0.50                    ( v4_orders_2 @ ( k3_waybel_2 @ A @ B @ C ) ) & 
% 0.20/0.50                    ( v7_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) ) & 
% 0.20/0.50                    ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t10_waybel_9])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l16_yellow_6, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ( v4_orders_2 @ A ) <=>
% 0.20/0.50         ( v4_orders_2 @
% 0.20/0.50           ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X3 : $i]:
% 0.20/0.50         (~ (v4_orders_2 @ X3)
% 0.20/0.50          | (v4_orders_2 @ 
% 0.20/0.50             (g1_orders_2 @ (u1_struct_0 @ X3) @ (u1_orders_2 @ X3)))
% 0.20/0.50          | ~ (l1_orders_2 @ X3)
% 0.20/0.50          | (v2_struct_0 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [l16_yellow_6])).
% 0.20/0.50  thf('2', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k3_waybel_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.20/0.50       ( ( v6_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) & 
% 0.20/0.50         ( l1_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.50          | ~ (l1_orders_2 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X12)
% 0.20/0.50          | ~ (l1_waybel_0 @ X12 @ X11)
% 0.20/0.50          | (l1_waybel_0 @ (k3_waybel_2 @ X11 @ X10 @ X12) @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k3_waybel_2])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.50  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain, ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf(d3_waybel_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( v6_waybel_0 @ D @ A ) & ( l1_waybel_0 @ D @ A ) ) =>
% 0.20/0.50                   ( ( ( D ) = ( k3_waybel_2 @ A @ B @ C ) ) <=>
% 0.20/0.50                     ( ( ( g1_orders_2 @
% 0.20/0.50                           ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) =
% 0.20/0.50                         ( g1_orders_2 @
% 0.20/0.50                           ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) & 
% 0.20/0.50                       ( ![E:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                           ( ?[F:$i]:
% 0.20/0.50                             ( ( ( k1_funct_1 @ ( u1_waybel_0 @ A @ D ) @ E ) =
% 0.20/0.50                                 ( k11_lattice3 @ A @ B @ F ) ) & 
% 0.20/0.50                               ( ( F ) =
% 0.20/0.50                                 ( k1_funct_1 @ ( u1_waybel_0 @ A @ C ) @ E ) ) & 
% 0.20/0.50                               ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (v6_waybel_0 @ X6 @ X5)
% 0.20/0.50          | ~ (l1_waybel_0 @ X6 @ X5)
% 0.20/0.50          | ((X6) != (k3_waybel_2 @ X5 @ X4 @ X7))
% 0.20/0.50          | ((g1_orders_2 @ (u1_struct_0 @ X6) @ (u1_orders_2 @ X6))
% 0.20/0.50              = (g1_orders_2 @ (u1_struct_0 @ X7) @ (u1_orders_2 @ X7)))
% 0.20/0.50          | ~ (l1_waybel_0 @ X7 @ X5)
% 0.20/0.50          | (v2_struct_0 @ X7)
% 0.20/0.50          | ~ (l1_orders_2 @ X5)
% 0.20/0.50          | (v2_struct_0 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_waybel_2])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X5)
% 0.20/0.50          | ~ (l1_orders_2 @ X5)
% 0.20/0.50          | (v2_struct_0 @ X7)
% 0.20/0.50          | ~ (l1_waybel_0 @ X7 @ X5)
% 0.20/0.50          | ((g1_orders_2 @ (u1_struct_0 @ (k3_waybel_2 @ X5 @ X4 @ X7)) @ 
% 0.20/0.50              (u1_orders_2 @ (k3_waybel_2 @ X5 @ X4 @ X7)))
% 0.20/0.50              = (g1_orders_2 @ (u1_struct_0 @ X7) @ (u1_orders_2 @ X7)))
% 0.20/0.50          | ~ (l1_waybel_0 @ (k3_waybel_2 @ X5 @ X4 @ X7) @ X5)
% 0.20/0.50          | ~ (v6_waybel_0 @ (k3_waybel_2 @ X5 @ X4 @ X7) @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.20/0.50        | ((g1_orders_2 @ (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.50            (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50            = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))
% 0.20/0.50        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.50  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.50          | ~ (l1_orders_2 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X12)
% 0.20/0.50          | ~ (l1_waybel_0 @ X12 @ X11)
% 0.20/0.50          | (v6_waybel_0 @ (k3_waybel_2 @ X11 @ X10 @ X12) @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k3_waybel_2])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '22'])).
% 0.20/0.50  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain, ((v6_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((((g1_orders_2 @ (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.50          (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50          = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16', '27', '28', '29'])).
% 0.20/0.50  thf('31', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((g1_orders_2 @ (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.50            (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50            = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C))))),
% 0.20/0.50      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((g1_orders_2 @ (u1_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.50         (u1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X3 : $i]:
% 0.20/0.50         (~ (v4_orders_2 @ 
% 0.20/0.50             (g1_orders_2 @ (u1_struct_0 @ X3) @ (u1_orders_2 @ X3)))
% 0.20/0.50          | (v4_orders_2 @ X3)
% 0.20/0.50          | ~ (l1_orders_2 @ X3)
% 0.20/0.50          | (v2_struct_0 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [l16_yellow_6])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((~ (v4_orders_2 @ 
% 0.20/0.50           (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))
% 0.20/0.50        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | ~ (l1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain, ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf(dt_l1_waybel_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (l1_waybel_0 @ X1 @ X2) | (l1_orders_2 @ X1) | ~ (l1_struct_0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((~ (l1_struct_0 @ sk_A)
% 0.20/0.50        | (l1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_l1_orders_2, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('41', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_orders_2 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.50  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain, ((l1_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((~ (v4_orders_2 @ 
% 0.20/0.50           (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))
% 0.20/0.50        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | ~ (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | ~ (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | ~ (l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((~ (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= (~ ((v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['45'])).
% 0.20/0.50  thf('47', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fc6_waybel_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( ~( v2_struct_0 @ C ) ) & ( v7_waybel_0 @ C ) & 
% 0.20/0.50         ( l1_waybel_0 @ C @ A ) ) =>
% 0.20/0.50       ( ( v6_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) & 
% 0.20/0.50         ( v7_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) ) ) ))).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (l1_orders_2 @ X17)
% 0.20/0.50          | (v2_struct_0 @ X17)
% 0.20/0.50          | (v2_struct_0 @ X18)
% 0.20/0.50          | ~ (v7_waybel_0 @ X18)
% 0.20/0.50          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.50          | (v7_waybel_0 @ (k3_waybel_2 @ X17 @ X16 @ X18)))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_waybel_2])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | ~ (v7_waybel_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | ~ (v7_waybel_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | ~ (v7_waybel_0 @ sk_C)
% 0.20/0.50        | (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '52'])).
% 0.20/0.50  thf('54', plain, ((v7_waybel_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('59', plain, ((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      ((~ (v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= (~ ((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['45'])).
% 0.20/0.50  thf('61', plain, (((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['45'])).
% 0.20/0.50  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fc5_waybel_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.20/0.50       ( ( ~( v2_struct_0 @ ( k3_waybel_2 @ A @ B @ C ) ) ) & 
% 0.20/0.50         ( v6_waybel_0 @ ( k3_waybel_2 @ A @ B @ C ) @ A ) ) ))).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.20/0.50          | ~ (l1_orders_2 @ X14)
% 0.20/0.50          | (v2_struct_0 @ X14)
% 0.20/0.50          | (v2_struct_0 @ X15)
% 0.20/0.50          | ~ (l1_waybel_0 @ X15 @ X14)
% 0.20/0.50          | ~ (v2_struct_0 @ (k3_waybel_2 @ X14 @ X13 @ X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc5_waybel_2])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A)
% 0.20/0.50         | (v2_struct_0 @ sk_C)
% 0.20/0.50         | ~ (l1_waybel_0 @ sk_C @ sk_A)))
% 0.20/0.50         <= (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['62', '67'])).
% 0.20/0.50  thf('69', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.20/0.50         <= (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C))
% 0.20/0.50         <= (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.50  thf('73', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain, (~ ((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.50  thf('75', plain, ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((~ (l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A))
% 0.20/0.50         <= (~ ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['45'])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (~ ((v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.50       ~ ((l1_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C) @ sk_A)) | 
% 0.20/0.50       ((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.50       ~ ((v7_waybel_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['45'])).
% 0.20/0.50  thf('79', plain, (~ ((v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['61', '74', '77', '78'])).
% 0.20/0.50  thf('80', plain, (~ (v4_orders_2 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['46', '79'])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | ~ (v4_orders_2 @ 
% 0.20/0.50             (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C))))),
% 0.20/0.50      inference('clc', [status(thm)], ['44', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C)
% 0.20/0.50        | ~ (l1_orders_2 @ sk_C)
% 0.20/0.50        | ~ (v4_orders_2 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '81'])).
% 0.20/0.50  thf('83', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (l1_waybel_0 @ X1 @ X2) | (l1_orders_2 @ X1) | ~ (l1_struct_0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.50  thf('85', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.50  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('87', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.50  thf('88', plain, ((v4_orders_2 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['82', '87', '88'])).
% 0.20/0.50  thf('90', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('91', plain, ((v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_struct_0 @ (k3_waybel_2 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | ~ (l1_waybel_0 @ sk_C @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.50  thf('94', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('95', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.50  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('97', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('clc', [status(thm)], ['95', '96'])).
% 0.20/0.50  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
