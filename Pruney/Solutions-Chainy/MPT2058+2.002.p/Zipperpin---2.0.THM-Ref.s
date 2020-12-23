%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgKqqEK6MN

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  266 ( 737 expanded)
%              Number of leaves         :   43 ( 248 expanded)
%              Depth                    :   36
%              Number of atoms          : 3489 (14265 expanded)
%              Number of equality atoms :   41 ( 190 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(t17_yellow19,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                <=> ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_yellow19])).

thf('0',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) ) ) )
      | ( X20
        = ( k2_yellow19 @ X21 @ ( k3_yellow19 @ X21 @ ( k2_struct_0 @ X21 ) @ X20 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('10',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) ) ) )
      | ( X20
        = ( k2_yellow19 @ X21 @ ( k3_yellow19 @ X21 @ ( k2_struct_0 @ X21 ) @ X20 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['15','18','21','24'])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_yellow_1 @ X14 ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ X14 ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X14 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('41',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('43',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X15 @ X14 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('48',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('49',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','54'])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('61',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X11 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('67',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('71',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','76'])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('82',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('83',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('84',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('86',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X8 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('87',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('88',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('90',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('93',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','98'])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['103'])).

thf('105',plain,(
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

thf('106',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r3_waybel_9 @ X18 @ X17 @ X19 )
      | ( r1_waybel_7 @ X18 @ ( k2_yellow19 @ X18 @ X17 ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('107',plain,(
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
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['80','113'])).

thf('115',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['58','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['32','117'])).

thf('119',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('120',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('121',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('123',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X8 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('124',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('125',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('126',plain,(
    ! [X7: $i] :
      ( ( k3_yellow_1 @ X7 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('127',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('130',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['120','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['119','135'])).

thf('137',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['118','136'])).

thf('138',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('143',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','147'])).

thf('149',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('152',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('153',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['103'])).

thf('169',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('170',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('171',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('172',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['103'])).

thf('173',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('174',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('175',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('176',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('177',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r1_waybel_7 @ X18 @ ( k2_yellow19 @ X18 @ X17 ) @ X19 )
      | ( r3_waybel_9 @ X18 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['172','187'])).

thf('189',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['119','135'])).

thf('194',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['170','202'])).

thf('204',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('208',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','167','168','220'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgKqqEK6MN
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 215 iterations in 0.118s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.57  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.57  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.57  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.21/0.57  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.57  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.57  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.57  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.57  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.57  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.21/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.21/0.57  thf(t17_yellow19, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.57             ( v1_subset_1 @
% 0.21/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.57             ( m1_subset_1 @
% 0.21/0.57               B @ 
% 0.21/0.57               ( k1_zfmisc_1 @
% 0.21/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57               ( ( r3_waybel_9 @
% 0.21/0.57                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.21/0.57                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.57            ( l1_pre_topc @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.57                ( v1_subset_1 @
% 0.21/0.57                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.57                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.57                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.57                ( m1_subset_1 @
% 0.21/0.57                  B @ 
% 0.21/0.57                  ( k1_zfmisc_1 @
% 0.21/0.57                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.57              ( ![C:$i]:
% 0.21/0.57                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57                  ( ( r3_waybel_9 @
% 0.21/0.57                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.21/0.57                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      ((~ (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.57        | ~ (r3_waybel_9 @ sk_A @ 
% 0.21/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.21/0.57       ~
% 0.21/0.57       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.57         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf(dt_l1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.57  thf('2', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.57  thf(d3_struct_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X4 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('4', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.57  thf('5', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d2_yellow_1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf(t15_yellow19, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58             ( v1_subset_1 @
% 0.21/0.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.58             ( m1_subset_1 @
% 0.21/0.58               B @ 
% 0.21/0.58               ( k1_zfmisc_1 @
% 0.21/0.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.58           ( ( B ) =
% 0.21/0.58             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X20)
% 0.21/0.58          | ~ (v1_subset_1 @ X20 @ 
% 0.21/0.58               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X21))))
% 0.21/0.58          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))
% 0.21/0.58          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))))
% 0.21/0.58          | ((X20)
% 0.21/0.58              = (k2_yellow19 @ X21 @ 
% 0.21/0.58                 (k3_yellow19 @ X21 @ (k2_struct_0 @ X21) @ X20)))
% 0.21/0.58          | ~ (l1_struct_0 @ X21)
% 0.21/0.58          | (v2_struct_0 @ X21))),
% 0.21/0.58      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X20)
% 0.21/0.58          | ~ (v1_subset_1 @ X20 @ 
% 0.21/0.58               (u1_struct_0 @ 
% 0.21/0.58                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21)))))
% 0.21/0.58          | ~ (v2_waybel_0 @ X20 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))
% 0.21/0.58          | ~ (v13_waybel_0 @ X20 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))
% 0.21/0.58          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ 
% 0.21/0.58                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))))
% 0.21/0.58          | ((X20)
% 0.21/0.58              = (k2_yellow19 @ X21 @ 
% 0.21/0.58                 (k3_yellow19 @ X21 @ (k2_struct_0 @ X21) @ X20)))
% 0.21/0.58          | ~ (l1_struct_0 @ X21)
% 0.21/0.58          | (v2_struct_0 @ X21))),
% 0.21/0.58      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | ((sk_B_1)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.58        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58        | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.21/0.58             (u1_struct_0 @ 
% 0.21/0.58              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['8', '14'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      ((v1_subset_1 @ sk_B_1 @ 
% 0.21/0.58        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      ((v1_subset_1 @ sk_B_1 @ 
% 0.21/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | ((sk_B_1)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.58      inference('demod', [status(thm)], ['15', '18', '21', '24'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | ((sk_B_1)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['5', '25'])).
% 0.21/0.58  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | ((sk_B_1)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.58  thf('29', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ((sk_B_1)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.21/0.58      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (((sk_B_1)
% 0.21/0.58         = (k2_yellow19 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('33', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf(dt_k2_subset_1, axiom,
% 0.21/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.58  thf('35', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.58  thf('36', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('37', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf(fc5_yellow19, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.58         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.21/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.21/0.58         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.58          | (v1_xboole_0 @ X14)
% 0.21/0.58          | ~ (l1_struct_0 @ X15)
% 0.21/0.58          | (v2_struct_0 @ X15)
% 0.21/0.58          | (v1_xboole_0 @ X16)
% 0.21/0.58          | ~ (v1_subset_1 @ X16 @ (u1_struct_0 @ (k3_yellow_1 @ X14)))
% 0.21/0.58          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.21/0.58          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.21/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X14))))
% 0.21/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.58          | (v1_xboole_0 @ X14)
% 0.21/0.58          | ~ (l1_struct_0 @ X15)
% 0.21/0.58          | (v2_struct_0 @ X15)
% 0.21/0.58          | (v1_xboole_0 @ X16)
% 0.21/0.58          | ~ (v1_subset_1 @ X16 @ 
% 0.21/0.58               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X14))))
% 0.21/0.58          | ~ (v2_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.21/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X14)))))
% 0.21/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.21/0.58      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.21/0.58               (u1_struct_0 @ 
% 0.21/0.58                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['39', '45'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      ((v1_subset_1 @ sk_B_1 @ 
% 0.21/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['38', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['37', '51'])).
% 0.21/0.58  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['36', '54'])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['33', '55'])).
% 0.21/0.58  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.58  thf('59', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('60', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('61', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf(fc4_yellow19, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.58         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.21/0.58         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.21/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.58          | (v1_xboole_0 @ X11)
% 0.21/0.58          | ~ (l1_struct_0 @ X12)
% 0.21/0.58          | (v2_struct_0 @ X12)
% 0.21/0.58          | (v1_xboole_0 @ X13)
% 0.21/0.58          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.21/0.58          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.21/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.21/0.58          | (v4_orders_2 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.58          | (v1_xboole_0 @ X11)
% 0.21/0.58          | ~ (l1_struct_0 @ X12)
% 0.21/0.58          | (v2_struct_0 @ X12)
% 0.21/0.58          | (v1_xboole_0 @ X13)
% 0.21/0.58          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.21/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.21/0.58          | (v4_orders_2 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.21/0.58      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.21/0.58  thf('69', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['63', '68'])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf('72', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.21/0.58  thf('73', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['62', '72'])).
% 0.21/0.58  thf('74', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['61', '73'])).
% 0.21/0.58  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('76', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.58  thf('77', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['60', '76'])).
% 0.21/0.58  thf('78', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['59', '77'])).
% 0.21/0.58  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('80', plain,
% 0.21/0.58      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.58  thf('81', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('82', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('83', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('84', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('85', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf(dt_k3_yellow19, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.21/0.58         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.58  thf('86', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X8))))
% 0.21/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X9 @ X8 @ X10) @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.21/0.58  thf('87', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('88', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('89', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('90', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X8)))))
% 0.21/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X9 @ X8 @ X10) @ X9))),
% 0.21/0.58      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.21/0.58  thf('91', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.58           X0)
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['85', '90'])).
% 0.21/0.58  thf('92', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('93', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf('94', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.58           X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.21/0.58  thf('95', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (l1_waybel_0 @ 
% 0.21/0.58             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['84', '94'])).
% 0.21/0.58  thf('96', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | (l1_waybel_0 @ 
% 0.21/0.58             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['83', '95'])).
% 0.21/0.58  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('98', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.58           X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.58  thf('99', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (l1_waybel_0 @ 
% 0.21/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['82', '98'])).
% 0.21/0.58  thf('100', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (l1_waybel_0 @ 
% 0.21/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['81', '99'])).
% 0.21/0.58  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('102', plain,
% 0.21/0.58      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.58         sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.58  thf('103', plain,
% 0.21/0.58      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.58        | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('104', plain,
% 0.21/0.58      (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['103'])).
% 0.21/0.58  thf('105', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t12_yellow19, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.58             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.21/0.58                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.58  thf('106', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X17)
% 0.21/0.58          | ~ (v4_orders_2 @ X17)
% 0.21/0.58          | ~ (v7_waybel_0 @ X17)
% 0.21/0.58          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.58          | ~ (r3_waybel_9 @ X18 @ X17 @ X19)
% 0.21/0.58          | (r1_waybel_7 @ X18 @ (k2_yellow19 @ X18 @ X17) @ X19)
% 0.21/0.58          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.58          | ~ (l1_pre_topc @ X18)
% 0.21/0.58          | ~ (v2_pre_topc @ X18)
% 0.21/0.58          | (v2_struct_0 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.21/0.58  thf('107', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.21/0.58          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.21/0.58          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ X0)
% 0.21/0.58          | ~ (v4_orders_2 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['105', '106'])).
% 0.21/0.58  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('110', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ sk_A)
% 0.21/0.58          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.21/0.58          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.21/0.58          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ X0)
% 0.21/0.58          | ~ (v4_orders_2 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.21/0.58  thf('111', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | ~ (v4_orders_2 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | ~ (v7_waybel_0 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | ~ (l1_waybel_0 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | (v2_struct_0 @ sk_A)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['104', '110'])).
% 0.21/0.58  thf('112', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | ~ (v7_waybel_0 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | ~ (v4_orders_2 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['102', '111'])).
% 0.21/0.58  thf('113', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | ~ (v4_orders_2 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | ~ (v7_waybel_0 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['112'])).
% 0.21/0.58  thf('114', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | ~ (v7_waybel_0 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['80', '113'])).
% 0.21/0.58  thf('115', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | ~ (v7_waybel_0 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['114'])).
% 0.21/0.58  thf('116', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['58', '115'])).
% 0.21/0.58  thf('117', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['116'])).
% 0.21/0.58  thf('118', plain,
% 0.21/0.58      ((((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['32', '117'])).
% 0.21/0.58  thf('119', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('120', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('121', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('122', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('123', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X8))))
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X9 @ X8 @ X10)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.21/0.58  thf('124', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('125', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('126', plain,
% 0.21/0.58      (![X7 : $i]: ((k3_yellow_1 @ X7) = (k3_lattice3 @ (k1_lattice3 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('127', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X8)))))
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X9 @ X8 @ X10)))),
% 0.21/0.58      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.21/0.58  thf('128', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['122', '127'])).
% 0.21/0.58  thf('129', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('130', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf('131', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.21/0.58  thf('132', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['121', '131'])).
% 0.21/0.58  thf('133', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['120', '132'])).
% 0.21/0.58  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('135', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['133', '134'])).
% 0.21/0.58  thf('136', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['119', '135'])).
% 0.21/0.58  thf('137', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['118', '136'])).
% 0.21/0.58  thf('138', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['137'])).
% 0.21/0.58  thf('139', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '138'])).
% 0.21/0.58  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('141', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['139', '140'])).
% 0.21/0.58  thf('142', plain,
% 0.21/0.58      ((~ (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('143', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['141', '142'])).
% 0.21/0.58  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('145', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['143', '144'])).
% 0.21/0.58  thf('146', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('147', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['145', '146'])).
% 0.21/0.58  thf('148', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['3', '147'])).
% 0.21/0.58  thf('149', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '148'])).
% 0.21/0.58  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('151', plain,
% 0.21/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['149', '150'])).
% 0.21/0.58  thf(rc7_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ?[B:$i]:
% 0.21/0.58         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('152', plain,
% 0.21/0.58      (![X6 : $i]:
% 0.21/0.58         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.58          | ~ (l1_pre_topc @ X6)
% 0.21/0.58          | ~ (v2_pre_topc @ X6)
% 0.21/0.58          | (v2_struct_0 @ X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.58  thf(cc1_subset_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.58  thf('153', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.21/0.58          | (v1_xboole_0 @ X2)
% 0.21/0.58          | ~ (v1_xboole_0 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.58  thf('154', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X0)
% 0.21/0.58          | ~ (v2_pre_topc @ X0)
% 0.21/0.58          | ~ (l1_pre_topc @ X0)
% 0.21/0.58          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.58          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['152', '153'])).
% 0.21/0.58  thf('155', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (sk_B @ sk_A))
% 0.21/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58         | (v2_struct_0 @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['151', '154'])).
% 0.21/0.58  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('158', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.21/0.58  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('160', plain,
% 0.21/0.58      (((v1_xboole_0 @ (sk_B @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['158', '159'])).
% 0.21/0.58  thf('161', plain,
% 0.21/0.58      (![X6 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ (sk_B @ X6))
% 0.21/0.58          | ~ (l1_pre_topc @ X6)
% 0.21/0.58          | ~ (v2_pre_topc @ X6)
% 0.21/0.58          | (v2_struct_0 @ X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.58  thf('162', plain,
% 0.21/0.58      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['160', '161'])).
% 0.21/0.58  thf('163', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('165', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['162', '163', '164'])).
% 0.21/0.58  thf('166', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('167', plain,
% 0.21/0.58      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.21/0.58       ~
% 0.21/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['165', '166'])).
% 0.21/0.58  thf('168', plain,
% 0.21/0.58      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.21/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.58      inference('split', [status(esa)], ['103'])).
% 0.21/0.58  thf('169', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('170', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('171', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('172', plain,
% 0.21/0.58      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C))
% 0.21/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['103'])).
% 0.21/0.58  thf('173', plain,
% 0.21/0.58      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.58  thf('174', plain,
% 0.21/0.58      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.58  thf('175', plain,
% 0.21/0.58      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.58         sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.58  thf('176', plain,
% 0.21/0.58      (((sk_B_1)
% 0.21/0.58         = (k2_yellow19 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('177', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X17)
% 0.21/0.58          | ~ (v4_orders_2 @ X17)
% 0.21/0.58          | ~ (v7_waybel_0 @ X17)
% 0.21/0.58          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.58          | ~ (r1_waybel_7 @ X18 @ (k2_yellow19 @ X18 @ X17) @ X19)
% 0.21/0.58          | (r3_waybel_9 @ X18 @ X17 @ X19)
% 0.21/0.58          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.58          | ~ (l1_pre_topc @ X18)
% 0.21/0.58          | ~ (v2_pre_topc @ X18)
% 0.21/0.58          | (v2_struct_0 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.21/0.58  thf('178', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | ~ (l1_waybel_0 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v4_orders_2 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['176', '177'])).
% 0.21/0.58  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('181', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | ~ (l1_waybel_0 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v4_orders_2 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['178', '179', '180'])).
% 0.21/0.58  thf('182', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v4_orders_2 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v7_waybel_0 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['175', '181'])).
% 0.21/0.58  thf('183', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | ~ (v7_waybel_0 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v4_orders_2 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['182'])).
% 0.21/0.58  thf('184', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | ~ (v4_orders_2 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['174', '183'])).
% 0.21/0.58  thf('185', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | ~ (v4_orders_2 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['184'])).
% 0.21/0.58  thf('186', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['173', '185'])).
% 0.21/0.58  thf('187', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['186'])).
% 0.21/0.58  thf('188', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)
% 0.21/0.58         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['172', '187'])).
% 0.21/0.58  thf('189', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('190', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))
% 0.21/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['188', '189'])).
% 0.21/0.58  thf('191', plain,
% 0.21/0.58      ((~ (r3_waybel_9 @ sk_A @ 
% 0.21/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('192', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['190', '191'])).
% 0.21/0.58  thf('193', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['119', '135'])).
% 0.21/0.58  thf('194', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['192', '193'])).
% 0.21/0.58  thf('195', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['194'])).
% 0.21/0.58  thf('196', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['171', '195'])).
% 0.21/0.58  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('198', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['196', '197'])).
% 0.21/0.58  thf('199', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('200', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['198', '199'])).
% 0.21/0.58  thf('201', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('202', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['200', '201'])).
% 0.21/0.58  thf('203', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['170', '202'])).
% 0.21/0.58  thf('204', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['169', '203'])).
% 0.21/0.58  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('206', plain,
% 0.21/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['204', '205'])).
% 0.21/0.58  thf('207', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X0)
% 0.21/0.58          | ~ (v2_pre_topc @ X0)
% 0.21/0.58          | ~ (l1_pre_topc @ X0)
% 0.21/0.58          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.58          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['152', '153'])).
% 0.21/0.58  thf('208', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (sk_B @ sk_A))
% 0.21/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58         | (v2_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['206', '207'])).
% 0.21/0.58  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('210', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('211', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['208', '209', '210'])).
% 0.21/0.58  thf('212', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('213', plain,
% 0.21/0.58      (((v1_xboole_0 @ (sk_B @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['211', '212'])).
% 0.21/0.58  thf('214', plain,
% 0.21/0.58      (![X6 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ (sk_B @ X6))
% 0.21/0.58          | ~ (l1_pre_topc @ X6)
% 0.21/0.58          | ~ (v2_pre_topc @ X6)
% 0.21/0.58          | (v2_struct_0 @ X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.58  thf('215', plain,
% 0.21/0.58      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['213', '214'])).
% 0.21/0.58  thf('216', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('218', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['215', '216', '217'])).
% 0.21/0.58  thf('219', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('220', plain,
% 0.21/0.58      (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.21/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['218', '219'])).
% 0.21/0.58  thf('221', plain, ($false),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['1', '167', '168', '220'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
