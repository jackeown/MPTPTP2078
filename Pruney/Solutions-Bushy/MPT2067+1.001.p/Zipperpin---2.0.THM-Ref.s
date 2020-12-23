%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2067+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C8K5pLMTlE

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:44 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  440 (51320 expanded)
%              Number of leaves         :   46 (13606 expanded)
%              Depth                    :   65
%              Number of atoms          : 7153 (1532428 expanded)
%              Number of equality atoms :   30 (2137 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_1_yellow19_type,type,(
    a_2_1_yellow19: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t27_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ? [D: $i] :
                    ( ( r1_waybel_7 @ A @ D @ C )
                    & ( r2_hidden @ B @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) )
                    & ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v1_subset_1 @ D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
                    & ~ ( v1_xboole_0 @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
                <=> ? [D: $i] :
                      ( ( r1_waybel_7 @ A @ D @ C )
                      & ( r2_hidden @ B @ D )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) )
                      & ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                      & ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                      & ( v1_subset_1 @ D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
                      & ~ ( v1_xboole_0 @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_yellow19])).

thf('4',plain,
    ( ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

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

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X13 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ~ ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,
    ( ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X41: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ sk_B @ X41 )
      | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C )
      | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_D_2 @ sk_C )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ? [D: $i] :
                    ( ( r3_waybel_9 @ A @ D @ C )
                    & ( r1_waybel_0 @ A @ D @ B )
                    & ( l1_waybel_0 @ D @ A )
                    & ( v7_waybel_0 @ D )
                    & ( v4_orders_2 @ D )
                    & ~ ( v2_struct_0 @ D ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X37 @ ( k2_pre_topc @ X36 @ X35 ) )
      | ( r1_waybel_0 @ X36 @ ( sk_D_1 @ X37 @ X35 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( k2_yellow19 @ A @ B ) )
            <=> ( ( r1_waybel_0 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( r1_waybel_0 @ X25 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r2_hidden @ X26 @ ( k2_yellow19 @ X25 @ X24 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_yellow19])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( k2_yellow19 @ sk_A @ X0 ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ sk_B @ ( k2_yellow19 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ sk_B @ ( k2_yellow19 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X37 @ ( k2_pre_topc @ X36 @ X35 ) )
      | ( l1_waybel_0 @ ( sk_D_1 @ X37 @ X35 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(d3_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( k2_yellow19 @ A @ B )
            = ( a_2_1_yellow19 @ A @ B ) ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( ( k2_yellow19 @ X1 @ X0 )
        = ( a_2_1_yellow19 @ X1 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_yellow19])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
        = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
        = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
        = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X37 @ ( k2_pre_topc @ X36 @ X35 ) )
      | ~ ( v2_struct_0 @ ( sk_D_1 @ X37 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
        = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X37 @ ( k2_pre_topc @ X36 @ X35 ) )
      | ( r3_waybel_9 @ X36 @ ( sk_D_1 @ X37 @ X35 @ X36 ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('95',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ~ ( r3_waybel_9 @ X29 @ X28 @ X30 )
      | ( r1_waybel_7 @ X29 @ ( k2_yellow19 @ X29 @ X28 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X37 @ ( k2_pre_topc @ X36 @ X35 ) )
      | ( v4_orders_2 @ ( sk_D_1 @ X37 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X37 @ ( k2_pre_topc @ X36 @ X35 ) )
      | ( v7_waybel_0 @ ( sk_D_1 @ X37 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('126',plain,
    ( ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','112','124','125','126'])).

thf('128',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( r1_waybel_7 @ sk_A @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('133',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(dt_k2_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k2_yellow19 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf('134',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X3 )
      | ( m1_subset_1 @ ( k2_yellow19 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X3 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow19])).

thf('135',plain,
    ( ( ( m1_subset_1 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('137',plain,
    ( ( ( m1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( m1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('144',plain,
    ( ( m1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('146',plain,
    ( ( ~ ( r1_waybel_7 @ sk_A @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ~ ( r2_hidden @ sk_B @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('148',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(fc2_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ~ ( v1_xboole_0 @ ( k2_yellow19 @ A @ B ) )
        & ( v13_waybel_0 @ ( k2_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )).

thf('149',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X9 )
      | ( v13_waybel_0 @ ( k2_yellow19 @ X9 @ X10 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow19])).

thf('150',plain,
    ( ( ( v13_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v13_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v13_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v13_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('157',plain,
    ( ( v13_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('159',plain,
    ( ( v13_waybel_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('161',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

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

thf('162',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ( v2_waybel_0 @ ( k2_yellow19 @ X11 @ X12 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow19])).

thf('163',plain,
    ( ( ( v2_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('165',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('166',plain,
    ( ( ( v2_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( v2_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('173',plain,
    ( ( v2_waybel_0 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('175',plain,
    ( ( v2_waybel_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('177',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('178',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ( v1_subset_1 @ ( k2_yellow19 @ X11 @ X12 ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X11 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow19])).

thf('179',plain,
    ( ( ( v1_subset_1 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('181',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('182',plain,
    ( ( ( v1_subset_1 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_subset_1 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','182'])).

thf('184',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_subset_1 @ ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('187',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( v1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('191',plain,
    ( ( v1_subset_1 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ~ ( r1_waybel_7 @ sk_A @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
      | ~ ( r2_hidden @ sk_B @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v1_xboole_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['146','159','175','191'])).

thf('193',plain,
    ( ( ( v1_xboole_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ sk_B @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','192'])).

thf('194',plain,
    ( ( v1_xboole_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','193'])).

thf('195',plain,
    ( ( ( k2_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('196',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X9 )
      | ~ ( v1_xboole_0 @ ( k2_yellow19 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow19])).

thf('197',plain,
    ( ( ~ ( v1_xboole_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('199',plain,
    ( ( ~ ( v1_xboole_0 @ ( a_2_1_yellow19 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['194','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('204',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','204'])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ~ ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( r1_waybel_7 @ sk_A @ X41 @ sk_C ) )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('209',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','208'])).

thf('210',plain,
    ( ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('211',plain,(
    v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','210'])).

thf('212',plain,
    ( ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('213',plain,(
    v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','212'])).

thf('214',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['18','209','211','213'])).

thf('215',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('216',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('217',plain,
    ( ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('218',plain,
    ( ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('219',plain,
    ( ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['219'])).

thf('221',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

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

thf('222',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ X17 ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ X17 ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X17 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('223',plain,
    ( ! [X0: $i] :
        ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ~ ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['220','223'])).

thf('225',plain,
    ( ! [X0: $i] :
        ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ~ ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['218','224'])).

thf('226',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['217','225'])).

thf('227',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['216','226'])).

thf('228',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['215','228'])).

thf('230',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','208'])).

thf('233',plain,(
    v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','210'])).

thf('234',plain,(
    v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','212'])).

thf('235',plain,
    ( ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['219'])).

thf('236',plain,(
    v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','235'])).

thf('237',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['231','232','233','234','236'])).

thf('238',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('239',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('240',plain,
    ( ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('241',plain,
    ( ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('242',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

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

thf('243',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v2_waybel_0 @ X7 @ ( k3_yellow_1 @ X5 ) )
      | ~ ( v13_waybel_0 @ X7 @ ( k3_yellow_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X5 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X6 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('244',plain,
    ( ! [X0: $i] :
        ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
        | ~ ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['241','244'])).

thf('246',plain,
    ( ! [X0: $i] :
        ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['240','245'])).

thf('247',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['239','246'])).

thf('248',plain,
    ( ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['238','248'])).

thf('250',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','208'])).

thf('253',plain,(
    v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','210'])).

thf('254',plain,(
    v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','212'])).

thf('255',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['251','252','253','254'])).

thf('256',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
   <= ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['256'])).

thf('258',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['256'])).

thf('259',plain,(
    r2_hidden @ sk_B @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['20','207','258'])).

thf('260',plain,(
    r2_hidden @ sk_B @ sk_D_2 ),
    inference(simpl_trail,[status(thm)],['257','259'])).

thf('261',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('262',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( ( k2_yellow19 @ X1 @ X0 )
        = ( a_2_1_yellow19 @ X1 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_yellow19])).

thf('264',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        = ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        = ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        = ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['261','265'])).

thf('267',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        = ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','208'])).

thf('270',plain,(
    v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','210'])).

thf('271',plain,(
    v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','212'])).

thf('272',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      = ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['268','269','270','271'])).

thf('273',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('274',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('275',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','208'])).

thf('276',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['274','275'])).

thf(t15_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('277',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_subset_1 @ X31 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) ) )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) ) ) )
      | ( X31
        = ( k2_yellow19 @ X32 @ ( k3_yellow19 @ X32 @ ( k2_struct_0 @ X32 ) @ X31 ) ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('278',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_D_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,
    ( ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('280',plain,(
    v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','210'])).

thf('281',plain,(
    v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['279','280'])).

thf('282',plain,
    ( ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('283',plain,(
    v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','212'])).

thf('284',plain,(
    v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['219'])).

thf('286',plain,(
    v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','235'])).

thf('287',plain,(
    v1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_D_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['278','281','284','287'])).

thf('289',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( sk_D_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['273','288'])).

thf('290',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( sk_D_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['289','290'])).

thf('292',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
   <= ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference(split,[status(esa)],['292'])).

thf('294',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['292'])).

thf('295',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['20','207','294'])).

thf('296',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['293','295'])).

thf('297',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ) ),
    inference(clc,[status(thm)],['291','296'])).

thf('298',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( sk_D_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['297','298'])).

thf('300',plain,
    ( ( sk_D_2
      = ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['272','299'])).

thf('301',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('302',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('303',plain,
    ( ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        = ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('304',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k2_yellow19 @ X25 @ X24 ) )
      | ( r1_waybel_0 @ X25 @ X24 @ X27 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_yellow19])).

thf('305',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
        | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_struct_0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
        | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A )
        | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A )
        | ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
        | ~ ( l1_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ~ ( r2_hidden @ X0 @ ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['305'])).

thf('307',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
        | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( l1_struct_0 @ sk_A )
        | ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['302','306'])).

thf('308',plain,
    ( ! [X0: $i] :
        ( ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
        | ~ ( l1_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ~ ( r2_hidden @ X0 @ ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
        | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['301','308'])).

thf('310',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
        | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['309','310'])).

thf('312',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','208'])).

thf('313',plain,(
    v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','210'])).

thf('314',plain,(
    v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','212'])).

thf('315',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['311','312','313','314'])).

thf('316',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['300','315'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['316'])).

thf('318',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['260','317'])).

thf('319',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_D_2 @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_D_2 @ sk_C ) ),
    inference(split,[status(esa)],['22'])).

thf('320',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_D_2 @ sk_C )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('321',plain,(
    r1_waybel_7 @ sk_A @ sk_D_2 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['20','207','320'])).

thf('322',plain,(
    r1_waybel_7 @ sk_A @ sk_D_2 @ sk_C ),
    inference(simpl_trail,[status(thm)],['319','321'])).

thf('323',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['18','209','211','213'])).

thf('324',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['231','232','233','234','236'])).

thf('325',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['251','252','253','254'])).

thf('326',plain,
    ( sk_D_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['297','298'])).

thf('327',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ~ ( r1_waybel_7 @ X29 @ ( k2_yellow19 @ X29 @ X28 ) @ X30 )
      | ( r3_waybel_9 @ X29 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('328',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_D_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['326','327'])).

thf('329',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_D_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['328','329','330'])).

thf('332',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['325','331'])).

thf('333',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['324','333'])).

thf('335',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['323','335'])).

thf('337',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['322','337'])).

thf('339',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_C ) ),
    inference(demod,[status(thm)],['338','339'])).

thf('341',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r3_waybel_9 @ X36 @ X38 @ X37 )
      | ~ ( r1_waybel_0 @ X36 @ X38 @ X35 )
      | ~ ( l1_waybel_0 @ X38 @ X36 )
      | ~ ( v7_waybel_0 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ( v2_struct_0 @ X38 )
      | ( r2_hidden @ X37 @ ( k2_pre_topc @ X36 @ X35 ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('344',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['344','345','346'])).

thf('348',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['341','347'])).

thf('349',plain,
    ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A )
    | ~ ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['340','348'])).

thf('350',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_B )
    | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['349'])).

thf('351',plain,
    ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['318','350'])).

thf('352',plain,
    ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['351'])).

thf('353',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['255','352'])).

thf('354',plain,
    ( ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['353'])).

thf('355',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['237','354'])).

thf('356',plain,
    ( ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','356'])).

thf('358',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('360',plain,
    ( ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('361',plain,
    ( ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('362',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('363',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v2_waybel_0 @ X7 @ ( k3_yellow_1 @ X5 ) )
      | ~ ( v13_waybel_0 @ X7 @ ( k3_yellow_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X5 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X6 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('364',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ~ ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['362','363'])).

thf('365',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_xboole_0 @ sk_D_2 )
        | ~ ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['361','364'])).

thf('366',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
        | ( v1_xboole_0 @ sk_D_2 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['360','365'])).

thf('367',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D_2 )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['359','366'])).

thf('368',plain,
    ( ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
      | ( v1_xboole_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['367'])).

thf('369',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','208'])).

thf('370',plain,(
    v13_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','210'])).

thf('371',plain,(
    v2_waybel_0 @ sk_D_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207','212'])).

thf('372',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_D_2 ) )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['368','369','370','371'])).

thf('373',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['358','372'])).

thf('374',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['373'])).

thf('375',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','374'])).

thf('376',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['375','376'])).

thf('378',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['19'])).

thf('379',plain,(
    ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['20','207'])).

thf('380',plain,(
    ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['378','379'])).

thf('381',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['377','380'])).

thf('382',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['381','382'])).

thf('384',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['293','295'])).

thf('385',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['383','384'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('386',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('387',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['385','386'])).

thf('388',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,(
    ~ ( l1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['387','388'])).

thf('390',plain,(
    ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','389'])).

thf('391',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,(
    $false ),
    inference(demod,[status(thm)],['390','391'])).


%------------------------------------------------------------------------------
