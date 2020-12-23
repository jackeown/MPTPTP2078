%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WkYLTeS7Z1

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 283 expanded)
%              Number of leaves         :   34 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          : 1375 (8962 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r1_waybel_3_type,type,(
    r1_waybel_3: $i > $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v3_waybel_7_type,type,(
    v3_waybel_7: $i > $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(t33_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) )
             => ( ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
                      & ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
                      & ( v3_waybel_7 @ D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) ) )
                   => ~ ( ( r2_hidden @ B @ D )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                           => ~ ( ( r2_hidden @ E @ C )
                                & ( r2_waybel_7 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) )
               => ( ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B @ C )
                 => ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
                        & ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
                        & ( v3_waybel_7 @ D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) ) )
                     => ~ ( ( r2_hidden @ B @ D )
                          & ! [E: $i] :
                              ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                             => ~ ( ( r2_hidden @ E @ C )
                                  & ( r2_waybel_7 @ A @ D @ E ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_waybel_7])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) )
             => ( ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( v1_subset_1 @ D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) )
                      & ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
                      & ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) ) )
                   => ~ ( ( r2_hidden @ B @ D )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                           => ~ ( ( r2_hidden @ E @ C )
                                & ( r1_waybel_7 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) ) )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) @ X16 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) ) ) )
      | ~ ( r2_hidden @ X16 @ X19 )
      | ( r1_waybel_7 @ X17 @ X19 @ ( sk_E @ X19 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_7])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ( r1_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ~ ( v1_xboole_0 @ B )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A )
              & ( v3_waybel_7 @ B @ A ) )
           => ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( v3_waybel_7 @ X10 @ X11 )
      | ~ ( v13_waybel_0 @ X10 @ X11 )
      | ~ ( v2_waybel_0 @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_waybel_7])).

thf('11',plain,
    ( ( v2_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_orders_2 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_orders_2 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v5_orders_2 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_waybel_7 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc7_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ~ ( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('13',plain,(
    ! [X8: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('14',plain,(
    ! [X9: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf(dt_k3_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('16',plain,(
    v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_waybel_7 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','16','17','18'])).

thf('20',plain,(
    ! [X5: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('21',plain,
    ( ( v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ( r1_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X0 @ sk_C )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ( r1_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    r2_hidden @ sk_B_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r1_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
            & ( v3_waybel_7 @ B @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) ) )
         => ! [C: $i] :
              ( ( r1_waybel_7 @ A @ B @ C )
            <=> ( r2_waybel_7 @ A @ B @ C ) ) ) ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ X13 ) ) ) ) )
      | ~ ( r1_waybel_7 @ X13 @ X12 @ X14 )
      | ( r2_waybel_7 @ X13 @ X12 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t31_waybel_7])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_D @ X0 )
      | ~ ( r1_waybel_7 @ sk_A @ sk_D @ X0 )
      | ~ ( v3_waybel_7 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_waybel_7 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_D @ X0 )
      | ~ ( r1_waybel_7 @ sk_A @ sk_D @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_waybel_7 @ sk_A @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_D @ X20 )
      | ~ ( r2_hidden @ X20 @ sk_C )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) ) )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) @ X16 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) ) ) )
      | ~ ( r2_hidden @ X16 @ X19 )
      | ( m1_subset_1 @ ( sk_E @ X19 @ X18 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_7])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X0 @ sk_C )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    r2_hidden @ sk_B_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) ) )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) @ X16 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ X17 ) ) ) ) )
      | ~ ( r2_hidden @ X16 @ X19 )
      | ( r2_hidden @ ( sk_E @ X19 @ X18 @ X17 ) @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_7])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v13_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_waybel_0 @ sk_D @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ X0 @ sk_C )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    r2_hidden @ sk_B_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['49','69','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WkYLTeS7Z1
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 51 iterations in 0.030s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.48  thf(r1_waybel_3_type, type, r1_waybel_3: $i > $i > $i > $o).
% 0.21/0.48  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.48  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.48  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v3_waybel_7_type, type, v3_waybel_7: $i > $i > $o).
% 0.21/0.48  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.21/0.48  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.48  thf(t33_waybel_7, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @
% 0.21/0.48             B @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @
% 0.21/0.48                 C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) =>
% 0.21/0.48               ( ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B @ C ) =>
% 0.21/0.48                 ( ![D:$i]:
% 0.21/0.48                   ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.48                       ( v2_waybel_0 @
% 0.21/0.48                         D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                       ( v13_waybel_0 @
% 0.21/0.48                         D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                       ( v3_waybel_7 @
% 0.21/0.48                         D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                       ( m1_subset_1 @
% 0.21/0.48                         D @ 
% 0.21/0.48                         ( k1_zfmisc_1 @
% 0.21/0.48                           ( u1_struct_0 @
% 0.21/0.48                             ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48                     ( ~( ( r2_hidden @ B @ D ) & 
% 0.21/0.48                          ( ![E:$i]:
% 0.21/0.48                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48                              ( ~( ( r2_hidden @ E @ C ) & 
% 0.21/0.48                                   ( r2_waybel_7 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @
% 0.21/0.48                B @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( m1_subset_1 @
% 0.21/0.48                    C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) =>
% 0.21/0.48                  ( ( r1_waybel_3 @
% 0.21/0.48                      ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B @ C ) =>
% 0.21/0.48                    ( ![D:$i]:
% 0.21/0.48                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.48                          ( v2_waybel_0 @
% 0.21/0.48                            D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                          ( v13_waybel_0 @
% 0.21/0.48                            D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                          ( v3_waybel_7 @
% 0.21/0.48                            D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                          ( m1_subset_1 @
% 0.21/0.48                            D @ 
% 0.21/0.48                            ( k1_zfmisc_1 @
% 0.21/0.48                              ( u1_struct_0 @
% 0.21/0.48                                ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48                        ( ~( ( r2_hidden @ B @ D ) & 
% 0.21/0.48                             ( ![E:$i]:
% 0.21/0.48                               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48                                 ( ~( ( r2_hidden @ E @ C ) & 
% 0.21/0.48                                      ( r2_waybel_7 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t33_waybel_7])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.48        (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ 
% 0.21/0.48        (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t32_waybel_7, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @
% 0.21/0.48             B @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @
% 0.21/0.48                 C @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) =>
% 0.21/0.48               ( ( r1_waybel_3 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B @ C ) =>
% 0.21/0.48                 ( ![D:$i]:
% 0.21/0.48                   ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.48                       ( v1_subset_1 @
% 0.21/0.48                         D @ 
% 0.21/0.48                         ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) & 
% 0.21/0.48                       ( v2_waybel_0 @
% 0.21/0.48                         D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                       ( v13_waybel_0 @
% 0.21/0.48                         D @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48                       ( m1_subset_1 @
% 0.21/0.48                         D @ 
% 0.21/0.48                         ( k1_zfmisc_1 @
% 0.21/0.48                           ( u1_struct_0 @
% 0.21/0.48                             ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48                     ( ~( ( r2_hidden @ B @ D ) & 
% 0.21/0.48                          ( ![E:$i]:
% 0.21/0.48                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48                              ( ~( ( r2_hidden @ E @ C ) & 
% 0.21/0.48                                   ( r1_waybel_7 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X16 @ 
% 0.21/0.48             (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X17))))
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ X17)) @ X16 @ X18)
% 0.21/0.48          | (v1_xboole_0 @ X19)
% 0.21/0.48          | ~ (v1_subset_1 @ X19 @ 
% 0.21/0.48               (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ X17))))
% 0.21/0.48          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))
% 0.21/0.48          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))
% 0.21/0.48          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))))
% 0.21/0.48          | ~ (r2_hidden @ X16 @ X19)
% 0.21/0.48          | (r1_waybel_7 @ X17 @ X19 @ (sk_E @ X19 @ X18 @ X17))
% 0.21/0.48          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X17))))
% 0.21/0.48          | ~ (l1_pre_topc @ X17)
% 0.21/0.48          | ~ (v2_pre_topc @ X17)
% 0.21/0.48          | (v2_struct_0 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [t32_waybel_7])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | (r1_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ X0 @ sk_A))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.48          | ~ (v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (v1_subset_1 @ sk_D @ 
% 0.21/0.48               (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X1 @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc1_waybel_7, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.21/0.48               ( v13_waybel_0 @ B @ A ) & ( v3_waybel_7 @ B @ A ) ) =>
% 0.21/0.48             ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48               ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.48               ( v2_waybel_0 @ B @ A ) & ( v13_waybel_0 @ B @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.48          | (v1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.21/0.48          | ~ (v3_waybel_7 @ X10 @ X11)
% 0.21/0.48          | ~ (v13_waybel_0 @ X10 @ X11)
% 0.21/0.48          | ~ (v2_waybel_0 @ X10 @ X11)
% 0.21/0.48          | (v1_xboole_0 @ X10)
% 0.21/0.48          | ~ (l1_orders_2 @ X11)
% 0.21/0.48          | ~ (v5_orders_2 @ X11)
% 0.21/0.48          | ~ (v4_orders_2 @ X11)
% 0.21/0.48          | ~ (v3_orders_2 @ X11)
% 0.21/0.48          | (v2_struct_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_waybel_7])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((v2_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | ~ (v3_orders_2 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | ~ (v4_orders_2 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | ~ (v5_orders_2 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | ~ (l1_orders_2 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | (v1_xboole_0 @ sk_D)
% 0.21/0.48        | ~ (v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | ~ (v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | ~ (v3_waybel_7 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | (v1_subset_1 @ sk_D @ 
% 0.21/0.48           (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf(fc7_yellow_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.48       ( v4_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.48       ( v3_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.48       ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.48       ( ~( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) ))).
% 0.21/0.48  thf('12', plain, (![X7 : $i]: (v3_orders_2 @ (k3_yellow_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.21/0.48  thf('13', plain, (![X8 : $i]: (v4_orders_2 @ (k3_yellow_1 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.21/0.48  thf('14', plain, (![X9 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.21/0.48  thf(dt_k3_yellow_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.48       ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ))).
% 0.21/0.48  thf('15', plain, (![X4 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k3_yellow_1])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((v3_waybel_7 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((v2_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | (v1_xboole_0 @ sk_D)
% 0.21/0.48        | (v1_subset_1 @ sk_D @ 
% 0.21/0.48           (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('demod', [status(thm)],
% 0.21/0.48                ['11', '12', '13', '14', '15', '16', '17', '18'])).
% 0.21/0.48  thf('20', plain, (![X5 : $i]: ~ (v2_struct_0 @ (k3_yellow_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((v1_subset_1 @ sk_D @ 
% 0.21/0.48         (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.48        | (v1_xboole_0 @ sk_D))),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((v1_subset_1 @ sk_D @ 
% 0.21/0.48        (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | (r1_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ X0 @ sk_A))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X1 @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5', '6', '7', '8', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.48             (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X0 @ sk_C)
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_D)
% 0.21/0.48          | (r1_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r1_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.21/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_D)
% 0.21/0.48        | (v1_xboole_0 @ sk_D)
% 0.21/0.48        | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ sk_B_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '25'])).
% 0.21/0.48  thf('27', plain, ((r2_hidden @ sk_B_1 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ sk_B_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r1_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.21/0.48        | (v1_xboole_0 @ sk_D))),
% 0.21/0.48      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.48  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_D)
% 0.21/0.48        | (r1_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain, ((r1_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t31_waybel_7, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48             ( v3_waybel_7 @ B @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.48             ( m1_subset_1 @
% 0.21/0.48               B @ 
% 0.21/0.48               ( k1_zfmisc_1 @
% 0.21/0.48                 ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( r1_waybel_7 @ A @ B @ C ) <=> ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X12)
% 0.21/0.48          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (u1_struct_0 @ X13)))
% 0.21/0.48          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (u1_struct_0 @ X13)))
% 0.21/0.48          | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (u1_struct_0 @ X13)))
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ X13)))))
% 0.21/0.48          | ~ (r1_waybel_7 @ X13 @ X12 @ X14)
% 0.21/0.48          | (r2_waybel_7 @ X13 @ X12 @ X14)
% 0.21/0.48          | ~ (l1_pre_topc @ X13)
% 0.21/0.48          | ~ (v2_pre_topc @ X13)
% 0.21/0.48          | (v2_struct_0 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t31_waybel_7])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | (r2_waybel_7 @ sk_A @ sk_D @ X0)
% 0.21/0.48          | ~ (r1_waybel_7 @ sk_A @ sk_D @ X0)
% 0.21/0.48          | ~ (v3_waybel_7 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | (v1_xboole_0 @ sk_D))),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      ((v3_waybel_7 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      ((v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | (r2_waybel_7 @ sk_A @ sk_D @ X0)
% 0.21/0.48          | ~ (r1_waybel_7 @ sk_A @ sk_D @ X0)
% 0.21/0.48          | (v1_xboole_0 @ sk_D))),
% 0.21/0.48      inference('demod', [status(thm)], ['36', '37', '38', '39', '40', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_D)
% 0.21/0.48        | (r2_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '42'])).
% 0.21/0.48  thf('44', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r2_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.48  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('47', plain, ((r2_waybel_7 @ sk_A @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X20 : $i]:
% 0.21/0.48         (~ (r2_waybel_7 @ sk_A @ sk_D @ X20)
% 0.21/0.48          | ~ (r2_hidden @ X20 @ sk_C)
% 0.21/0.48          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      ((~ (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | ~ (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ sk_B_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ 
% 0.21/0.48        (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X16 @ 
% 0.21/0.48             (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X17))))
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ X17)) @ X16 @ X18)
% 0.21/0.48          | (v1_xboole_0 @ X19)
% 0.21/0.48          | ~ (v1_subset_1 @ X19 @ 
% 0.21/0.48               (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ X17))))
% 0.21/0.48          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))
% 0.21/0.48          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))
% 0.21/0.48          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))))
% 0.21/0.48          | ~ (r2_hidden @ X16 @ X19)
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ X19 @ X18 @ X17) @ (u1_struct_0 @ X17))
% 0.21/0.48          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X17))))
% 0.21/0.48          | ~ (l1_pre_topc @ X17)
% 0.21/0.48          | ~ (v2_pre_topc @ X17)
% 0.21/0.48          | (v2_struct_0 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [t32_waybel_7])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ sk_D @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.48          | ~ (v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (v1_subset_1 @ sk_D @ 
% 0.21/0.48               (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X1 @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.48  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      ((v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      ((v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      ((v1_subset_1 @ sk_D @ 
% 0.21/0.48        (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ sk_D @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X1 @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.48      inference('demod', [status(thm)], ['54', '55', '56', '57', '58', '59'])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.48             (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X0 @ sk_C)
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_D)
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['51', '60'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_D)
% 0.21/0.48        | (v1_xboole_0 @ sk_D)
% 0.21/0.48        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.21/0.48             (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['50', '61'])).
% 0.21/0.48  thf('63', plain, ((r2_hidden @ sk_B_1 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('64', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.48        (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('65', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | (v1_xboole_0 @ sk_D))),
% 0.21/0.48      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.21/0.48  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_D)
% 0.21/0.48        | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.48  thf('68', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('69', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.48  thf('70', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.48        (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('71', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ 
% 0.21/0.48        (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('72', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('73', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X16 @ 
% 0.21/0.48             (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X17))))
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ X17)) @ X16 @ X18)
% 0.21/0.48          | (v1_xboole_0 @ X19)
% 0.21/0.48          | ~ (v1_subset_1 @ X19 @ 
% 0.21/0.48               (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ X17))))
% 0.21/0.48          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))
% 0.21/0.48          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))
% 0.21/0.48          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ X17)))))
% 0.21/0.48          | ~ (r2_hidden @ X16 @ X19)
% 0.21/0.48          | (r2_hidden @ (sk_E @ X19 @ X18 @ X17) @ X18)
% 0.21/0.48          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X17))))
% 0.21/0.48          | ~ (l1_pre_topc @ X17)
% 0.21/0.48          | ~ (v2_pre_topc @ X17)
% 0.21/0.48          | (v2_struct_0 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [t32_waybel_7])).
% 0.21/0.48  thf('74', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.48          | ~ (v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48          | ~ (v1_subset_1 @ sk_D @ 
% 0.21/0.48               (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X1 @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.48  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('77', plain,
% 0.21/0.48      ((v13_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('78', plain,
% 0.21/0.48      ((v2_waybel_0 @ sk_D @ (k3_yellow_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('79', plain,
% 0.21/0.48      ((v1_subset_1 @ sk_D @ 
% 0.21/0.48        (u1_struct_0 @ (k3_yellow_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('80', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_D)
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X1 @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.48               (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.48      inference('demod', [status(thm)], ['74', '75', '76', '77', '78', '79'])).
% 0.21/0.48  thf('81', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.48             (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))
% 0.21/0.48          | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ X0 @ sk_C)
% 0.21/0.48          | (v1_xboole_0 @ sk_D)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_D)
% 0.21/0.48          | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_C)
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['71', '80'])).
% 0.21/0.48  thf('82', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_C)
% 0.21/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_D)
% 0.21/0.48        | (v1_xboole_0 @ sk_D)
% 0.21/0.48        | ~ (r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ sk_B_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['70', '81'])).
% 0.21/0.48  thf('83', plain, ((r2_hidden @ sk_B_1 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('84', plain,
% 0.21/0.48      ((r1_waybel_3 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)) @ sk_B_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('85', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_C)
% 0.21/0.48        | (v1_xboole_0 @ sk_D))),
% 0.21/0.48      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.21/0.48  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('87', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_D) | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_C))),
% 0.21/0.48      inference('clc', [status(thm)], ['85', '86'])).
% 0.21/0.48  thf('88', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('89', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_C)),
% 0.21/0.48      inference('clc', [status(thm)], ['87', '88'])).
% 0.21/0.48  thf('90', plain, ($false),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '69', '89'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
