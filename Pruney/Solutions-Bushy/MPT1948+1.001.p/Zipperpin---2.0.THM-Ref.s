%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1948+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.td8mTVtqdc

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:35 EST 2020

% Result     : Theorem 2.86s
% Output     : Refutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  310 (2496 expanded)
%              Number of leaves         :   38 ( 716 expanded)
%              Depth                    :   73
%              Number of atoms          : 7071 (55371 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   24 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(k5_yellow_6_type,type,(
    k5_yellow_6: $i > $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t46_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ~ ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
                  & ! [D: $i] :
                      ( ( m2_yellow_6 @ D @ A @ B )
                     => ? [E: $i] :
                          ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ E ) )
                          & ( m2_yellow_6 @ E @ A @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ~ ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
                    & ! [D: $i] :
                        ( ( m2_yellow_6 @ D @ A @ B )
                       => ? [E: $i] :
                            ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ E ) )
                            & ( m2_yellow_6 @ E @ A @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_yellow_6])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ~ ( r2_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( l1_waybel_0 @ X36 @ X37 )
      | ( r2_waybel_0 @ X37 @ X36 @ ( k6_subset_1 @ ( u1_struct_0 @ X37 ) @ X38 ) )
      | ( r1_waybel_0 @ X37 @ X36 @ X38 )
      | ~ ( l1_struct_0 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t31_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
             => ( m2_yellow_6 @ ( k5_yellow_6 @ A @ B @ C ) @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( l1_waybel_0 @ X29 @ X30 )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ X30 @ X29 @ X31 ) @ X30 @ X29 )
      | ~ ( r2_waybel_0 @ X30 @ X29 @ X31 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_yellow_6])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(dt_m2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m2_yellow_6 @ C @ A @ B )
         => ( ~ ( v2_struct_0 @ C )
            & ( v4_orders_2 @ C )
            & ( v7_waybel_0 @ C )
            & ( l1_waybel_0 @ C @ A ) ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( v4_orders_2 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( v7_waybel_0 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('46',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,(
    ! [X40: $i] :
      ( ( m2_yellow_6 @ ( sk_E_2 @ X40 ) @ sk_A @ X40 )
      | ~ ( m2_yellow_6 @ X40 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( v4_orders_2 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_yellow_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v6_waybel_0 @ ( k5_yellow_6 @ A @ B @ C ) @ A )
        & ( m1_yellow_6 @ ( k5_yellow_6 @ A @ B @ C ) @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( l1_struct_0 @ X9 )
      | ( m1_yellow_6 @ ( k5_yellow_6 @ X9 @ X8 @ X10 ) @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_yellow_6])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A @ sk_B )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X13 @ X12 )
      | ( l1_waybel_0 @ X14 @ X12 )
      | ~ ( m1_yellow_6 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['44','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('78',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('80',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( v7_waybel_0 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['76','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('94',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('96',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( l1_waybel_0 @ X17 @ X15 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('111',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('112',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf(d18_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k10_yellow_6 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_connsp_2 @ E @ A @ D )
                         => ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) )).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( X2
       != ( k10_yellow_6 @ X1 @ X0 ) )
      | ( r2_hidden @ X4 @ X2 )
      | ( m1_connsp_2 @ ( sk_E_1 @ X4 @ X0 @ X1 ) @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X4 @ X0 @ X1 ) @ X1 @ X4 )
      | ( r2_hidden @ X4 @ ( k10_yellow_6 @ X1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','123'])).

thf('125',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('136',plain,(
    ! [X40: $i] :
      ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ X40 ) ) )
      | ~ ( m2_yellow_6 @ X40 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('141',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['139','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['138','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( X2
       != ( k10_yellow_6 @ X1 @ X0 ) )
      | ~ ( m1_connsp_2 @ X5 @ X1 @ X4 )
      | ( r1_waybel_0 @ X1 @ X0 @ X5 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ ( k10_yellow_6 @ X1 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X5 )
      | ~ ( m1_connsp_2 @ X5 @ X1 @ X4 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( m1_connsp_2 @ X2 @ sk_A @ X1 )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','152'])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( m1_connsp_2 @ X2 @ sk_A @ X1 )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X2 )
      | ~ ( m1_connsp_2 @ X2 @ sk_A @ X1 )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['137','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['134','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['133','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf(t28_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
             => ( r2_waybel_0 @ A @ B @ C ) ) ) ) )).

thf('170',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v7_waybel_0 @ X26 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ( r2_waybel_0 @ X27 @ X26 @ X28 )
      | ~ ( r1_waybel_0 @ X27 @ X26 @ X28 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow_6])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['108','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t27_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m2_yellow_6 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( r2_waybel_0 @ A @ C @ D )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) )).

thf('184',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v7_waybel_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ~ ( r2_waybel_0 @ X23 @ X24 @ X25 )
      | ( r2_waybel_0 @ X23 @ X22 @ X25 )
      | ~ ( m2_yellow_6 @ X24 @ X23 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_6])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['182','188'])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('199',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t32_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( m2_yellow_6 @ D @ A @ B )
             => ( ( D
                  = ( k5_yellow_6 @ A @ B @ C ) )
               => ( r1_waybel_0 @ A @ D @ C ) ) ) ) ) )).

thf('201',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X33 )
      | ( X35
       != ( k5_yellow_6 @ X33 @ X32 @ X34 ) )
      | ( r1_waybel_0 @ X33 @ X35 @ X34 )
      | ~ ( m2_yellow_6 @ X35 @ X33 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t32_yellow_6])).

thf('202',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_struct_0 @ X33 )
      | ~ ( m2_yellow_6 @ ( k5_yellow_6 @ X33 @ X32 @ X34 ) @ X33 @ X32 )
      | ( r1_waybel_0 @ X33 @ ( k5_yellow_6 @ X33 @ X32 @ X34 ) @ X34 )
      | ~ ( l1_waybel_0 @ X32 @ X33 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','202'])).

thf('204',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['199','208'])).

thf('210',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('212',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( r2_waybel_0 @ X19 @ X18 @ X21 )
      | ~ ( r1_waybel_0 @ X19 @ X18 @ ( k6_subset_1 @ ( u1_struct_0 @ X19 ) @ X21 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['198','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['197','219'])).

thf('221',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('224',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ~ ( v2_struct_0 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['222','228'])).

thf('230',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['221','231'])).

thf('233',plain,
    ( ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','233'])).

thf('235',plain,
    ( ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','235'])).

thf('237',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('240',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ~ ( v2_struct_0 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['241','242','243','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['238','246'])).

thf('248',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['237','249'])).

thf('251',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('253',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( X2
       != ( k10_yellow_6 @ X1 @ X0 ) )
      | ( r2_hidden @ X4 @ X2 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ ( sk_E_1 @ X4 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('254',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ ( sk_E_1 @ X4 @ X0 @ X1 ) )
      | ( r2_hidden @ X4 @ ( k10_yellow_6 @ X1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['252','254'])).

thf('256',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['255','256','257','258','259','260'])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['251','261'])).

thf('263',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,(
    ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['267','268'])).

thf('270',plain,(
    $false ),
    inference(demod,[status(thm)],['0','269'])).


%------------------------------------------------------------------------------
