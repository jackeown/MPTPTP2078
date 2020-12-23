%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G1xFcKCMxv

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 753 expanded)
%              Number of leaves         :   44 ( 252 expanded)
%              Depth                    :   32
%              Number of atoms          : 3418 (14643 expanded)
%              Number of equality atoms :   41 ( 190 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X9 @ ( k1_connsp_2 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_subset_1 @ X24 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) ) )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) ) ) )
      | ( X24
        = ( k2_yellow19 @ X25 @ ( k3_yellow19 @ X25 @ ( k2_struct_0 @ X25 ) @ X24 ) ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_subset_1 @ X24 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) ) ) )
      | ( X24
        = ( k2_yellow19 @ X25 @ ( k3_yellow19 @ X25 @ ( k2_struct_0 @ X25 ) @ X24 ) ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','26','29','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('48',plain,(
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

thf('49',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('51',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_xboole_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X19 @ X18 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('56',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('57',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','62'])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('69',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('72',plain,(
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

thf('73',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('74',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('75',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X16 @ X15 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('79',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','84'])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('90',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('91',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('94',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('95',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('96',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('97',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('98',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('101',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['91','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','106'])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,(
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

thf('114',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( r3_waybel_9 @ X22 @ X21 @ X23 )
      | ( r1_waybel_7 @ X22 @ ( k2_yellow19 @ X22 @ X21 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('115',plain,(
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
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['110','119'])).

thf('121',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['88','121'])).

thf('123',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['66','123'])).

thf('125',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['40','125'])).

thf('127',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('128',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('129',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('131',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('132',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('133',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('134',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('135',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('138',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['129','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','143'])).

thf('145',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['126','144'])).

thf('146',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('151',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['11','155'])).

thf('157',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('161',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('162',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('168',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','169'])).

thf('171',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','170'])).

thf('172',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['111'])).

thf('173',plain,(
    r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('174',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('175',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('176',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('177',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['111'])).

thf('178',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('179',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('180',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('181',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('182',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( r1_waybel_7 @ X22 @ ( k2_yellow19 @ X22 @ X21 ) @ X23 )
      | ( r3_waybel_9 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['180','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['177','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('197',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','143'])).

thf('199',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','200'])).

thf('202',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['175','207'])).

thf('209',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['174','208'])).

thf('210',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('213',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['173','213'])).

thf('215',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','171','172','214'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G1xFcKCMxv
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 197 iterations in 0.106s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.57  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.20/0.57  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.20/0.57  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.20/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.57  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.20/0.57  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.57  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.57  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.57  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.57  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.57  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.20/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.57  thf(t17_yellow19, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57             ( v1_subset_1 @
% 0.20/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57             ( m1_subset_1 @
% 0.20/0.57               B @ 
% 0.20/0.57               ( k1_zfmisc_1 @
% 0.20/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.57               ( ( r3_waybel_9 @
% 0.20/0.57                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.20/0.57                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.57            ( l1_pre_topc @ A ) ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57                ( v1_subset_1 @
% 0.20/0.57                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.57                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57                ( m1_subset_1 @
% 0.20/0.57                  B @ 
% 0.20/0.57                  ( k1_zfmisc_1 @
% 0.20/0.57                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.57              ( ![C:$i]:
% 0.20/0.57                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.57                  ( ( r3_waybel_9 @
% 0.20/0.57                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.20/0.57                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.20/0.57        | ~ (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.57       ~
% 0.20/0.57       ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t30_connsp_2, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.57           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.20/0.57          | (r2_hidden @ X9 @ (k1_connsp_2 @ X10 @ X9))
% 0.20/0.57          | ~ (l1_pre_topc @ X10)
% 0.20/0.57          | ~ (v2_pre_topc @ X10)
% 0.20/0.57          | (v2_struct_0 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A)
% 0.20/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.57  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.57  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('9', plain, ((r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C))),
% 0.20/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf(dt_l1_pre_topc, axiom,
% 0.20/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.57  thf('10', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf(d3_struct_0, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X5 : $i]:
% 0.20/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.57  thf('12', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('13', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(d2_yellow_1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf(t15_yellow19, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57             ( v1_subset_1 @
% 0.20/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57             ( m1_subset_1 @
% 0.20/0.57               B @ 
% 0.20/0.57               ( k1_zfmisc_1 @
% 0.20/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.57           ( ( B ) =
% 0.20/0.57             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X24 : $i, X25 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X24)
% 0.20/0.57          | ~ (v1_subset_1 @ X24 @ 
% 0.20/0.57               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X25))))
% 0.20/0.57          | ~ (v2_waybel_0 @ X24 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))
% 0.20/0.57          | ~ (v13_waybel_0 @ X24 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))
% 0.20/0.57          | ~ (m1_subset_1 @ X24 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))))
% 0.20/0.57          | ((X24)
% 0.20/0.57              = (k2_yellow19 @ X25 @ 
% 0.20/0.57                 (k3_yellow19 @ X25 @ (k2_struct_0 @ X25) @ X24)))
% 0.20/0.57          | ~ (l1_struct_0 @ X25)
% 0.20/0.57          | (v2_struct_0 @ X25))),
% 0.20/0.57      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X24 : $i, X25 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X24)
% 0.20/0.57          | ~ (v1_subset_1 @ X24 @ 
% 0.20/0.57               (u1_struct_0 @ 
% 0.20/0.57                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25)))))
% 0.20/0.57          | ~ (v2_waybel_0 @ X24 @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))
% 0.20/0.57          | ~ (v13_waybel_0 @ X24 @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))
% 0.20/0.57          | ~ (m1_subset_1 @ X24 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ 
% 0.20/0.57                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))))
% 0.20/0.57          | ((X24)
% 0.20/0.57              = (k2_yellow19 @ X25 @ 
% 0.20/0.57                 (k3_yellow19 @ X25 @ (k2_struct_0 @ X25) @ X24)))
% 0.20/0.57          | ~ (l1_struct_0 @ X25)
% 0.20/0.57          | (v2_struct_0 @ X25))),
% 0.20/0.57      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A)
% 0.20/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k2_yellow19 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | ~ (v13_waybel_0 @ sk_B @ 
% 0.20/0.57             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57        | ~ (v2_waybel_0 @ sk_B @ 
% 0.20/0.57             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57        | ~ (v1_subset_1 @ sk_B @ 
% 0.20/0.57             (u1_struct_0 @ 
% 0.20/0.57              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.20/0.57        | (v1_xboole_0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      ((v1_subset_1 @ sk_B @ 
% 0.20/0.57        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      ((v1_subset_1 @ sk_B @ 
% 0.20/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A)
% 0.20/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k2_yellow19 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | (v1_xboole_0 @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['23', '26', '29', '32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k2_yellow19 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | (v2_struct_0 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['13', '33'])).
% 0.20/0.57  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (((v1_xboole_0 @ sk_B)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k2_yellow19 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | (v2_struct_0 @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.57  thf('37', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k2_yellow19 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.57      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.57  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (((sk_B)
% 0.20/0.57         = (k2_yellow19 @ sk_A @ 
% 0.20/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('41', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf(dt_k2_subset_1, axiom,
% 0.20/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.57  thf('43', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.20/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.57  thf('44', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.57  thf('45', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (![X5 : $i]:
% 0.20/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf(fc5_yellow19, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.20/0.57         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.20/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.20/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.20/0.57         ( m1_subset_1 @
% 0.20/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.20/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.20/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.20/0.57         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.57          | (v1_xboole_0 @ X18)
% 0.20/0.57          | ~ (l1_struct_0 @ X19)
% 0.20/0.57          | (v2_struct_0 @ X19)
% 0.20/0.57          | (v1_xboole_0 @ X20)
% 0.20/0.57          | ~ (v1_subset_1 @ X20 @ (u1_struct_0 @ (k3_yellow_1 @ X18)))
% 0.20/0.57          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.20/0.57          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.20/0.57          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X18))))
% 0.20/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.57          | (v1_xboole_0 @ X18)
% 0.20/0.57          | ~ (l1_struct_0 @ X19)
% 0.20/0.57          | (v2_struct_0 @ X19)
% 0.20/0.57          | (v1_xboole_0 @ X20)
% 0.20/0.57          | ~ (v1_subset_1 @ X20 @ 
% 0.20/0.57               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18))))
% 0.20/0.57          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.20/0.57          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.20/0.57          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 0.20/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.20/0.57      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | ~ (v1_subset_1 @ sk_B @ 
% 0.20/0.57               (u1_struct_0 @ 
% 0.20/0.57                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['47', '53'])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      ((v1_subset_1 @ sk_B @ 
% 0.20/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['46', '58'])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['45', '59'])).
% 0.20/0.57  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['44', '62'])).
% 0.20/0.57  thf('64', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['41', '63'])).
% 0.20/0.57  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.57  thf('67', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('68', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.57  thf('69', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('70', plain,
% 0.20/0.57      (![X5 : $i]:
% 0.20/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.57  thf('71', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf(fc4_yellow19, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.20/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.20/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.20/0.57         ( m1_subset_1 @
% 0.20/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.20/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.20/0.57         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.20/0.57         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.20/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.20/0.57  thf('72', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.57          | (v1_xboole_0 @ X15)
% 0.20/0.57          | ~ (l1_struct_0 @ X16)
% 0.20/0.57          | (v2_struct_0 @ X16)
% 0.20/0.57          | (v1_xboole_0 @ X17)
% 0.20/0.57          | ~ (v2_waybel_0 @ X17 @ (k3_yellow_1 @ X15))
% 0.20/0.57          | ~ (v13_waybel_0 @ X17 @ (k3_yellow_1 @ X15))
% 0.20/0.57          | ~ (m1_subset_1 @ X17 @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X15))))
% 0.20/0.57          | (v4_orders_2 @ (k3_yellow19 @ X16 @ X15 @ X17)))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('75', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('76', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.57          | (v1_xboole_0 @ X15)
% 0.20/0.57          | ~ (l1_struct_0 @ X16)
% 0.20/0.57          | (v2_struct_0 @ X16)
% 0.20/0.57          | (v1_xboole_0 @ X17)
% 0.20/0.57          | ~ (v2_waybel_0 @ X17 @ (k3_lattice3 @ (k1_lattice3 @ X15)))
% 0.20/0.57          | ~ (v13_waybel_0 @ X17 @ (k3_lattice3 @ (k1_lattice3 @ X15)))
% 0.20/0.57          | ~ (m1_subset_1 @ X17 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X15)))))
% 0.20/0.57          | (v4_orders_2 @ (k3_yellow19 @ X16 @ X15 @ X17)))),
% 0.20/0.57      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.20/0.57  thf('77', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['71', '76'])).
% 0.20/0.57  thf('78', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('79', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('80', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.20/0.57  thf('81', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['70', '80'])).
% 0.20/0.57  thf('82', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['69', '81'])).
% 0.20/0.57  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('84', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.57  thf('85', plain,
% 0.20/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['68', '84'])).
% 0.20/0.57  thf('86', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['67', '85'])).
% 0.20/0.57  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('88', plain,
% 0.20/0.57      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.57  thf('89', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('90', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.57  thf('91', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('92', plain,
% 0.20/0.57      (![X5 : $i]:
% 0.20/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.57  thf('93', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf(dt_k3_yellow19, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.20/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.20/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.20/0.57         ( m1_subset_1 @
% 0.20/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.20/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.20/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.20/0.57         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.20/0.57  thf('94', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.57          | (v1_xboole_0 @ X12)
% 0.20/0.57          | ~ (l1_struct_0 @ X13)
% 0.20/0.57          | (v2_struct_0 @ X13)
% 0.20/0.57          | (v1_xboole_0 @ X14)
% 0.20/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.20/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.20/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.20/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14) @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.20/0.57  thf('95', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('96', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('97', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('98', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.57          | (v1_xboole_0 @ X12)
% 0.20/0.57          | ~ (l1_struct_0 @ X13)
% 0.20/0.57          | (v2_struct_0 @ X13)
% 0.20/0.57          | (v1_xboole_0 @ X14)
% 0.20/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.20/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.20/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.20/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14) @ X13))),
% 0.20/0.57      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 0.20/0.57  thf('99', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['93', '98'])).
% 0.20/0.57  thf('100', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('101', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('102', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.20/0.57  thf('103', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57             X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['92', '102'])).
% 0.20/0.57  thf('104', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57             X0)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['91', '103'])).
% 0.20/0.57  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('106', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.57  thf('107', plain,
% 0.20/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57           sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['90', '106'])).
% 0.20/0.57  thf('108', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57           sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['89', '107'])).
% 0.20/0.57  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('110', plain,
% 0.20/0.57      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57         sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.57  thf('111', plain,
% 0.20/0.57      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.20/0.57        | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('112', plain,
% 0.20/0.57      (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('split', [status(esa)], ['111'])).
% 0.20/0.57  thf('113', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t12_yellow19, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.57             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.57               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.20/0.57                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.20/0.57  thf('114', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X21)
% 0.20/0.57          | ~ (v4_orders_2 @ X21)
% 0.20/0.57          | ~ (v7_waybel_0 @ X21)
% 0.20/0.57          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.20/0.57          | ~ (r3_waybel_9 @ X22 @ X21 @ X23)
% 0.20/0.57          | (r1_waybel_7 @ X22 @ (k2_yellow19 @ X22 @ X21) @ X23)
% 0.20/0.57          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.57          | ~ (l1_pre_topc @ X22)
% 0.20/0.57          | ~ (v2_pre_topc @ X22)
% 0.20/0.57          | (v2_struct_0 @ X22))),
% 0.20/0.57      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.20/0.57  thf('115', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_A)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.20/0.57          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.20/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.57          | ~ (v7_waybel_0 @ X0)
% 0.20/0.57          | ~ (v4_orders_2 @ X0)
% 0.20/0.57          | (v2_struct_0 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.57  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('118', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_A)
% 0.20/0.57          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.20/0.57          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.20/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.57          | ~ (v7_waybel_0 @ X0)
% 0.20/0.57          | ~ (v4_orders_2 @ X0)
% 0.20/0.57          | (v2_struct_0 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.20/0.57  thf('119', plain,
% 0.20/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | ~ (l1_waybel_0 @ 
% 0.20/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ 
% 0.20/0.57            (k2_yellow19 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57            sk_C)
% 0.20/0.57         | (v2_struct_0 @ sk_A)))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['112', '118'])).
% 0.20/0.57  thf('120', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ 
% 0.20/0.57            (k2_yellow19 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57            sk_C)
% 0.20/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['110', '119'])).
% 0.20/0.57  thf('121', plain,
% 0.20/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ 
% 0.20/0.57            (k2_yellow19 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57            sk_C)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['120'])).
% 0.20/0.57  thf('122', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ 
% 0.20/0.57            (k2_yellow19 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57            sk_C)
% 0.20/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['88', '121'])).
% 0.20/0.57  thf('123', plain,
% 0.20/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ 
% 0.20/0.57            (k2_yellow19 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57            sk_C)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['122'])).
% 0.20/0.57  thf('124', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ 
% 0.20/0.57            (k2_yellow19 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57            sk_C)
% 0.20/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['66', '123'])).
% 0.20/0.57  thf('125', plain,
% 0.20/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ 
% 0.20/0.57            (k2_yellow19 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57            sk_C)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['124'])).
% 0.20/0.57  thf('126', plain,
% 0.20/0.57      ((((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['40', '125'])).
% 0.20/0.57  thf('127', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.57  thf('128', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('129', plain,
% 0.20/0.57      (![X5 : $i]:
% 0.20/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.57  thf('130', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('131', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.57          | (v1_xboole_0 @ X12)
% 0.20/0.57          | ~ (l1_struct_0 @ X13)
% 0.20/0.57          | (v2_struct_0 @ X13)
% 0.20/0.57          | (v1_xboole_0 @ X14)
% 0.20/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.20/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.20/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.20/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.20/0.57  thf('132', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('133', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('134', plain,
% 0.20/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('135', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.57          | (v1_xboole_0 @ X12)
% 0.20/0.57          | ~ (l1_struct_0 @ X13)
% 0.20/0.57          | (v2_struct_0 @ X13)
% 0.20/0.57          | (v1_xboole_0 @ X14)
% 0.20/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.20/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.20/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.20/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.20/0.57      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.20/0.57  thf('136', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['130', '135'])).
% 0.20/0.57  thf('137', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('138', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('139', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.20/0.57  thf('140', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['129', '139'])).
% 0.20/0.57  thf('141', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['128', '140'])).
% 0.20/0.57  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('143', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (l1_struct_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['141', '142'])).
% 0.20/0.57  thf('144', plain,
% 0.20/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['127', '143'])).
% 0.20/0.57  thf('145', plain,
% 0.20/0.57      ((((v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['126', '144'])).
% 0.20/0.57  thf('146', plain,
% 0.20/0.57      (((~ (l1_struct_0 @ sk_A)
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['145'])).
% 0.20/0.57  thf('147', plain,
% 0.20/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '146'])).
% 0.20/0.57  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('149', plain,
% 0.20/0.57      ((((v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.57         <= (((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['147', '148'])).
% 0.20/0.57  thf('150', plain,
% 0.20/0.57      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.20/0.57         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('151', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)))
% 0.20/0.57         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['149', '150'])).
% 0.20/0.57  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('153', plain,
% 0.20/0.57      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('clc', [status(thm)], ['151', '152'])).
% 0.20/0.57  thf('154', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('155', plain,
% 0.20/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.20/0.57         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('clc', [status(thm)], ['153', '154'])).
% 0.20/0.57  thf('156', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.57         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['11', '155'])).
% 0.20/0.57  thf('157', plain,
% 0.20/0.57      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.57         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['10', '156'])).
% 0.20/0.57  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('159', plain,
% 0.20/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['157', '158'])).
% 0.20/0.57  thf('160', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(dt_k1_connsp_2, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.57         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57       ( m1_subset_1 @
% 0.20/0.57         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.57  thf('161', plain,
% 0.20/0.57      (![X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (l1_pre_topc @ X7)
% 0.20/0.57          | ~ (v2_pre_topc @ X7)
% 0.20/0.57          | (v2_struct_0 @ X7)
% 0.20/0.57          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.57          | (m1_subset_1 @ (k1_connsp_2 @ X7 @ X8) @ 
% 0.20/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.20/0.57  thf('162', plain,
% 0.20/0.57      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.20/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['160', '161'])).
% 0.20/0.57  thf('163', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('165', plain,
% 0.20/0.57      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.20/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57        | (v2_struct_0 @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['162', '163', '164'])).
% 0.20/0.57  thf('166', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('167', plain,
% 0.20/0.57      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('clc', [status(thm)], ['165', '166'])).
% 0.20/0.57  thf(t5_subset, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.57  thf('168', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.57          | ~ (v1_xboole_0 @ X4)
% 0.20/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.57  thf('169', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['167', '168'])).
% 0.20/0.57  thf('170', plain,
% 0.20/0.57      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))
% 0.20/0.57         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['159', '169'])).
% 0.20/0.57  thf('171', plain,
% 0.20/0.57      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.57       ~
% 0.20/0.57       ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '170'])).
% 0.20/0.57  thf('172', plain,
% 0.20/0.57      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.57       ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.20/0.57      inference('split', [status(esa)], ['111'])).
% 0.20/0.57  thf('173', plain, ((r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C))),
% 0.20/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('174', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('175', plain,
% 0.20/0.57      (![X5 : $i]:
% 0.20/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.57  thf('176', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.57  thf('177', plain,
% 0.20/0.57      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.20/0.57         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('split', [status(esa)], ['111'])).
% 0.20/0.57  thf('178', plain,
% 0.20/0.57      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.57  thf('179', plain,
% 0.20/0.57      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.57  thf('180', plain,
% 0.20/0.57      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57         sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.57  thf('181', plain,
% 0.20/0.57      (((sk_B)
% 0.20/0.57         = (k2_yellow19 @ sk_A @ 
% 0.20/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('182', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X21)
% 0.20/0.57          | ~ (v4_orders_2 @ X21)
% 0.20/0.57          | ~ (v7_waybel_0 @ X21)
% 0.20/0.57          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.20/0.57          | ~ (r1_waybel_7 @ X22 @ (k2_yellow19 @ X22 @ X21) @ X23)
% 0.20/0.57          | (r3_waybel_9 @ X22 @ X21 @ X23)
% 0.20/0.57          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.57          | ~ (l1_pre_topc @ X22)
% 0.20/0.57          | ~ (v2_pre_topc @ X22)
% 0.20/0.57          | (v2_struct_0 @ X22))),
% 0.20/0.57      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.20/0.57  thf('183', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | ~ (l1_waybel_0 @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['181', '182'])).
% 0.20/0.57  thf('184', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('186', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | ~ (l1_waybel_0 @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.20/0.57  thf('187', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['180', '186'])).
% 0.20/0.57  thf('188', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['187'])).
% 0.20/0.57  thf('189', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['179', '188'])).
% 0.20/0.57  thf('190', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['189'])).
% 0.20/0.57  thf('191', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['178', '190'])).
% 0.20/0.57  thf('192', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.20/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (v1_xboole_0 @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ sk_A)
% 0.20/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['191'])).
% 0.20/0.57  thf('193', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.20/0.57         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.20/0.57         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['177', '192'])).
% 0.20/0.57  thf('194', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('195', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | (r3_waybel_9 @ sk_A @ 
% 0.20/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.20/0.57         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['193', '194'])).
% 0.20/0.57  thf('196', plain,
% 0.20/0.57      ((~ (r3_waybel_9 @ sk_A @ 
% 0.20/0.57           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('197', plain,
% 0.20/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['195', '196'])).
% 0.20/0.57  thf('198', plain,
% 0.20/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57        | (v2_struct_0 @ sk_A)
% 0.20/0.57        | (v1_xboole_0 @ sk_B)
% 0.20/0.57        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['127', '143'])).
% 0.20/0.57  thf('199', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['197', '198'])).
% 0.20/0.57  thf('200', plain,
% 0.20/0.57      (((~ (l1_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['199'])).
% 0.20/0.57  thf('201', plain,
% 0.20/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['176', '200'])).
% 0.20/0.57  thf('202', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('203', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57         | (v2_struct_0 @ sk_A)
% 0.20/0.57         | (v1_xboole_0 @ sk_B)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['201', '202'])).
% 0.20/0.57  thf('204', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('205', plain,
% 0.20/0.57      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('clc', [status(thm)], ['203', '204'])).
% 0.20/0.57  thf('206', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('207', plain,
% 0.20/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('clc', [status(thm)], ['205', '206'])).
% 0.20/0.57  thf('208', plain,
% 0.20/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['175', '207'])).
% 0.20/0.57  thf('209', plain,
% 0.20/0.57      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['174', '208'])).
% 0.20/0.57  thf('210', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('211', plain,
% 0.20/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['209', '210'])).
% 0.20/0.57  thf('212', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['167', '168'])).
% 0.20/0.57  thf('213', plain,
% 0.20/0.57      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.20/0.57             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['211', '212'])).
% 0.20/0.57  thf('214', plain,
% 0.20/0.57      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.57       ((r3_waybel_9 @ sk_A @ 
% 0.20/0.57         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['173', '213'])).
% 0.20/0.57  thf('215', plain, ($false),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['1', '171', '172', '214'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.43/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
