%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2074+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JFxwuNXszb

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:45 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  329 ( 856 expanded)
%              Number of leaves         :   45 ( 236 expanded)
%              Depth                    :   48
%              Number of atoms          : 9597 (25892 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_yellow_6_type,type,(
    k6_yellow_6: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t34_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_compts_1 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ? [C: $i] :
                ( ( r1_waybel_7 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( v1_compts_1 @ A )
        <=> ! [B: $i] :
              ( ( ~ ( v1_xboole_0 @ B )
                & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
                & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
             => ? [C: $i] :
                  ( ( r1_waybel_7 @ A @ B @ C )
                  & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_yellow19])).

thf('0',plain,(
    ! [X37: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) )
      | ( v1_compts_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) )
    | ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 )
      | ~ ( v1_compts_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
        | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['12'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    ! [X37: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_compts_1 @ sk_A_1 )
   <= ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('22',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('23',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('24',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(fc5_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A )
        & ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_xboole_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_yellow_1 @ X18 ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_yellow_1 @ X18 ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_yellow_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X18 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_B_2 )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( ~ ( l1_struct_0 @ sk_A_1 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('38',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('39',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(fc4_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_yellow_1 @ X15 ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_yellow_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X15 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_B_2 )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('52',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('53',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(dt_k3_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A )
        & ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ) )).

thf('55',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v2_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( v13_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X4 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X5 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ X0 )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_B_2 )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ X0 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ X0 )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,
    ( ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(l37_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_compts_1 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ? [C: $i] :
                ( ( r3_waybel_9 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_compts_1 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v7_waybel_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X21 )
      | ( m1_subset_1 @ ( sk_C @ X22 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l37_yellow19])).

thf('65',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v1_compts_1 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v1_compts_1 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ~ ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v1_compts_1 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','69'])).

thf('71',plain,
    ( ( ~ ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v1_compts_1 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','71'])).

thf('73',plain,
    ( ( ~ ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','73'])).

thf('75',plain,
    ( ( v1_compts_1 @ sk_A_1 )
   <= ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('76',plain,
    ( ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('78',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('79',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_compts_1 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v7_waybel_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X21 )
      | ( r3_waybel_9 @ X21 @ X22 @ ( sk_C @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l37_yellow19])).

thf('80',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v1_compts_1 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v1_compts_1 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ~ ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v1_compts_1 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,
    ( ( ~ ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ~ ( v1_compts_1 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,
    ( ( ~ ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['75','88'])).

thf('90',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('91',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('92',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t17_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_waybel_9 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C )
              <=> ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) )).

thf('94',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) ) ) )
      | ~ ( r3_waybel_9 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) @ X30 )
      | ( r1_waybel_7 @ X29 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow19])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A_1 )
        | ~ ( v2_pre_topc @ sk_A_1 )
        | ~ ( l1_pre_topc @ sk_A_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A_1 ) )
        | ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X0 )
        | ~ ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ X0 )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A_1 ) )
        | ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X0 )
        | ~ ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ X0 )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_B_2 )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ X0 )
        | ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A_1 ) )
        | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A_1 ) )
        | ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X0 )
        | ~ ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ X0 )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_B_2 )
        | ~ ( r3_waybel_9 @ sk_A_1 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ X0 )
        | ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A_1 ) )
        | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','101'])).

thf('103',plain,
    ( ( ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) ) )
   <= ( ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','103'])).

thf('105',plain,
    ( ( ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','73'])).

thf('107',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
        | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
   <= ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
        | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ ( sk_C @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) @ sk_A_1 ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('112',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('113',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('115',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v2_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( v13_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X4 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X5 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
        | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_B_2 )
        | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
        | ( v1_xboole_0 @ sk_B_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,
    ( ( ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','118'])).

thf('120',plain,
    ( ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A_1 @ ( k2_struct_0 @ sk_A_1 ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','120'])).

thf('122',plain,
    ( ( ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['16','127'])).

thf('129',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('132',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('133',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( l1_struct_0 @ sk_A_1 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
      & ( v1_compts_1 @ sk_A_1 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
      & ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['12'])).

thf('140',plain,
    ( ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
    | ~ ( v1_compts_1 @ sk_A_1 )
    | ~ ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A_1 ) )
          | ~ ( r1_waybel_7 @ sk_A_1 @ sk_B_2 @ X36 ) )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
    | ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(l38_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ~ ( ( r2_hidden @ B @ ( k6_yellow_6 @ A ) )
                & ! [C: $i] :
                    ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                   => ~ ( r3_waybel_9 @ A @ B @ C ) ) ) )
       => ( v1_compts_1 @ A ) ) ) )).

thf('143',plain,(
    ! [X24: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('144',plain,(
    ! [X24: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X24 ) )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('145',plain,(
    ! [X24: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X24 ) )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('146',plain,(
    ! [X24: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('147',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('148',plain,(
    ! [X24: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X24 ) )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('149',plain,(
    ! [X24: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X24 ) )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('150',plain,(
    ! [X24: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf(fc3_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_subset_1 @ ( k2_yellow19 @ A @ B ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
        & ( v2_waybel_0 @ ( k2_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )).

thf('151',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X13 @ X14 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow19])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X24: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf(fc2_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ~ ( v1_xboole_0 @ ( k2_yellow19 @ A @ B ) )
        & ( v13_waybel_0 @ ( k2_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )).

thf('159',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ( v13_waybel_0 @ ( k2_yellow19 @ X11 @ X12 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow19])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v13_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v13_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X24: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X24 ) )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('163',plain,(
    ! [X24: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X24 ) )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('164',plain,(
    ! [X24: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('165',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( v1_subset_1 @ ( k2_yellow19 @ X13 @ X14 ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X13 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow19])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X24: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf(dt_k2_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k2_yellow19 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf('173',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_waybel_0 @ X3 @ X2 )
      | ( m1_subset_1 @ ( k2_yellow19 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X2 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow19])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( m1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('177',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v1_subset_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v1_subset_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['171','180'])).

thf('182',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['161','185'])).

thf('187',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['157','190'])).

thf('192',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['147','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v13_waybel_0 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_yellow19 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('204',plain,
    ( ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('205',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v1_subset_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v1_subset_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['202','208'])).

thf('210',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,
    ( ( ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( v13_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['201','213'])).

thf('215',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,
    ( ( ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( v2_waybel_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['200','218'])).

thf('220',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ( ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['199','223'])).

thf('225',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( r1_waybel_7 @ sk_A_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf(t12_yellow19,axiom,(
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
             => ( ( r3_waybel_9 @ A @ B @ C )
              <=> ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('227',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( l1_waybel_0 @ X25 @ X26 )
      | ~ ( r1_waybel_7 @ X26 @ ( k2_yellow19 @ X26 @ X25 ) @ X27 )
      | ( r3_waybel_9 @ X26 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('228',plain,
    ( ( ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A_1 ) @ sk_A_1 )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A_1 ) @ sk_A_1 )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A_1 ) @ sk_A_1 )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,
    ( ( ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A_1 ) @ sk_A_1 )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['198','232'])).

thf('234',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A_1 ) @ sk_A_1 )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['233'])).

thf('235',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','234'])).

thf('236',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','239'])).

thf('241',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','244'])).

thf('246',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['245','246','247'])).

thf('249',plain,
    ( ( ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) @ ( u1_struct_0 @ sk_A_1 ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('251',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r3_waybel_9 @ X24 @ ( sk_B_1 @ X24 ) @ X23 )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('252',plain,
    ( ( ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ~ ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ~ ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) @ ( sk_C_1 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) ) )
   <= ! [X37: $i] :
        ( ( v1_xboole_0 @ X37 )
        | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
        | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
        | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['249','256'])).

thf('258',plain,
    ( ( ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_xboole_0 @ ( k2_yellow19 @ sk_A_1 @ ( sk_B_1 @ sk_A_1 ) ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ~ ( v1_xboole_0 @ ( k2_yellow19 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow19])).

thf('260',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A_1 ) @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( l1_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,
    ( ( ~ ( l1_struct_0 @ sk_A_1 )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A_1 ) @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','261'])).

thf('263',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ~ ( l1_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('266',plain,
    ( ( ~ ( l1_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,
    ( ( ~ ( l1_pre_topc @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','266'])).

thf('268',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['267','268'])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( ( v2_struct_0 @ ( sk_B_1 @ sk_A_1 ) )
      | ( v1_compts_1 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(clc,[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X24: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B_1 @ X24 ) )
      | ( v1_compts_1 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('273',plain,
    ( ( ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['271','272'])).

thf('274',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( ( v1_compts_1 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['273','274','275'])).

thf('277',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v1_compts_1 @ sk_A_1 ) )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( v1_compts_1 @ sk_A_1 )
   <= ( ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
      & ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ) ),
    inference(clc,[status(thm)],['277','278'])).

thf('280',plain,
    ( ~ ( v1_compts_1 @ sk_A_1 )
   <= ~ ( v1_compts_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('281',plain,
    ( ~ ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( m1_subset_1 @ ( sk_C_1 @ X37 ) @ ( u1_struct_0 @ sk_A_1 ) ) )
    | ( v1_compts_1 @ sk_A_1 )
    | ~ ! [X37: $i] :
          ( ( v1_xboole_0 @ X37 )
          | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) )
          | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) )
          | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A_1 ) ) ) ) )
          | ( r1_waybel_7 @ sk_A_1 @ X37 @ ( sk_C_1 @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['279','280'])).

thf('282',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','13','140','141','281'])).


%------------------------------------------------------------------------------
