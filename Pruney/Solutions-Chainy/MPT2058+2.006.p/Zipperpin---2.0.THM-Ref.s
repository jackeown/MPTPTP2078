%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XZCL1xbKoq

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:49 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  250 ( 709 expanded)
%              Number of leaves         :   40 ( 236 expanded)
%              Depth                    :   34
%              Number of atoms          : 3348 (13409 expanded)
%              Number of equality atoms :   41 ( 190 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

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

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_subset_1 @ X22 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X23 ) ) ) )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_yellow_1 @ ( k2_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_yellow_1 @ ( k2_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X23 ) ) ) ) )
      | ( X22
        = ( k2_yellow19 @ X23 @ ( k3_yellow19 @ X23 @ ( k2_struct_0 @ X23 ) @ X22 ) ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_subset_1 @ X22 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X23 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X23 ) ) ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X23 ) ) ) ) ) )
      | ( X22
        = ( k2_yellow19 @ X23 @ ( k3_yellow19 @ X23 @ ( k2_struct_0 @ X23 ) @ X22 ) ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','19','22','25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_yellow_1 @ X16 ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X16 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('50',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('51',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','56'])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('63',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('66',plain,(
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

thf('67',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('68',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('69',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('70',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('73',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','78'])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('85',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('88',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('89',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('90',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('91',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('92',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('95',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','100'])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['105'])).

thf('107',plain,(
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

thf('108',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r3_waybel_9 @ X20 @ X19 @ X21 )
      | ( r1_waybel_7 @ X20 @ ( k2_yellow19 @ X20 @ X19 ) @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('109',plain,(
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
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
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
    inference('sup-',[status(thm)],['82','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['60','117'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['33','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('122',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('123',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('125',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('126',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('127',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('128',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('129',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['125','126','127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('132',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['122','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','137'])).

thf('139',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['120','138'])).

thf('140',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','149'])).

thf('151',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('154',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['105'])).

thf('162',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('163',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('164',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('165',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('166',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['105'])).

thf('167',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('168',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('169',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('170',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('171',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r1_waybel_7 @ X20 @ ( k2_yellow19 @ X20 @ X19 ) @ X21 )
      | ( r3_waybel_9 @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('172',plain,(
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
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
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
    inference('sup-',[status(thm)],['169','175'])).

thf('177',plain,(
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
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
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
    inference('sup-',[status(thm)],['168','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
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
    inference('sup-',[status(thm)],['167','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['166','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','137'])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['165','189'])).

thf('191',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['164','196'])).

thf('198',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','204'])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','160','161','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XZCL1xbKoq
% 0.13/0.36  % Computer   : n023.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 13:10:21 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 197 iterations in 0.101s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.38/0.58  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.38/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.38/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.58  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.38/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.58  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.38/0.58  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.38/0.58  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.38/0.58  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.38/0.58  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.38/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.58  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.38/0.58  thf(t17_yellow19, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58             ( v1_subset_1 @
% 0.38/0.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.58             ( m1_subset_1 @
% 0.38/0.58               B @ 
% 0.38/0.58               ( k1_zfmisc_1 @
% 0.38/0.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58               ( ( r3_waybel_9 @
% 0.38/0.58                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.38/0.58                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58            ( l1_pre_topc @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58                ( v1_subset_1 @
% 0.38/0.58                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.58                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.58                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.58                ( m1_subset_1 @
% 0.38/0.58                  B @ 
% 0.38/0.58                  ( k1_zfmisc_1 @
% 0.38/0.58                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.58              ( ![C:$i]:
% 0.38/0.58                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58                  ( ( r3_waybel_9 @
% 0.38/0.58                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.38/0.58                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.58        | ~ (r3_waybel_9 @ sk_A @ 
% 0.38/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.58       ~
% 0.38/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.38/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.58      inference('split', [status(esa)], ['0'])).
% 0.38/0.58  thf(dt_l1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.58  thf('2', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('3', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf(d3_struct_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X6 : $i]:
% 0.38/0.58         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.58  thf('5', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('6', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(d2_yellow_1, axiom,
% 0.38/0.58    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf(t15_yellow19, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58             ( v1_subset_1 @
% 0.38/0.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.58             ( m1_subset_1 @
% 0.38/0.58               B @ 
% 0.38/0.58               ( k1_zfmisc_1 @
% 0.38/0.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.58           ( ( B ) =
% 0.38/0.58             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X22)
% 0.38/0.58          | ~ (v1_subset_1 @ X22 @ 
% 0.38/0.58               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X23))))
% 0.38/0.58          | ~ (v2_waybel_0 @ X22 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))
% 0.38/0.58          | ~ (v13_waybel_0 @ X22 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))
% 0.38/0.58          | ~ (m1_subset_1 @ X22 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))))
% 0.38/0.58          | ((X22)
% 0.38/0.58              = (k2_yellow19 @ X23 @ 
% 0.38/0.58                 (k3_yellow19 @ X23 @ (k2_struct_0 @ X23) @ X22)))
% 0.38/0.58          | ~ (l1_struct_0 @ X23)
% 0.38/0.58          | (v2_struct_0 @ X23))),
% 0.38/0.58      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X22)
% 0.38/0.58          | ~ (v1_subset_1 @ X22 @ 
% 0.38/0.58               (u1_struct_0 @ 
% 0.38/0.58                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23)))))
% 0.38/0.58          | ~ (v2_waybel_0 @ X22 @ 
% 0.38/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))
% 0.38/0.58          | ~ (v13_waybel_0 @ X22 @ 
% 0.38/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))
% 0.38/0.58          | ~ (m1_subset_1 @ X22 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (u1_struct_0 @ 
% 0.38/0.58                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))))
% 0.38/0.58          | ((X22)
% 0.38/0.58              = (k2_yellow19 @ X23 @ 
% 0.38/0.58                 (k3_yellow19 @ X23 @ (k2_struct_0 @ X23) @ X22)))
% 0.38/0.58          | ~ (l1_struct_0 @ X23)
% 0.38/0.58          | (v2_struct_0 @ X23))),
% 0.38/0.58      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58        | ((sk_B)
% 0.38/0.58            = (k2_yellow19 @ sk_A @ 
% 0.38/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.58        | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.58        | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.58        | ~ (v1_subset_1 @ sk_B @ 
% 0.38/0.58             (u1_struct_0 @ 
% 0.38/0.58              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.58        | (v1_xboole_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '15'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      ((v1_subset_1 @ sk_B @ 
% 0.38/0.58        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      ((v1_subset_1 @ sk_B @ 
% 0.38/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58        | ((sk_B)
% 0.38/0.58            = (k2_yellow19 @ sk_A @ 
% 0.38/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.58        | (v1_xboole_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['16', '19', '22', '25'])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | ((sk_B)
% 0.38/0.58            = (k2_yellow19 @ sk_A @ 
% 0.38/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '26'])).
% 0.38/0.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B)
% 0.38/0.58        | ((sk_B)
% 0.38/0.58            = (k2_yellow19 @ sk_A @ 
% 0.38/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf('30', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ((sk_B)
% 0.38/0.58            = (k2_yellow19 @ sk_A @ 
% 0.38/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.38/0.58  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (((sk_B)
% 0.38/0.58         = (k2_yellow19 @ sk_A @ 
% 0.38/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.58      inference('clc', [status(thm)], ['31', '32'])).
% 0.38/0.58  thf('34', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf(d10_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.58  thf(t3_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (![X3 : $i, X5 : $i]:
% 0.38/0.58         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.58  thf('38', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('39', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X6 : $i]:
% 0.38/0.58         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf(fc5_yellow19, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.58         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.38/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @
% 0.38/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.38/0.58         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.58          | (v1_xboole_0 @ X16)
% 0.38/0.58          | ~ (l1_struct_0 @ X17)
% 0.38/0.58          | (v2_struct_0 @ X17)
% 0.38/0.58          | (v1_xboole_0 @ X18)
% 0.38/0.58          | ~ (v1_subset_1 @ X18 @ (u1_struct_0 @ (k3_yellow_1 @ X16)))
% 0.38/0.58          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.38/0.58          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.38/0.58          | ~ (m1_subset_1 @ X18 @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X16))))
% 0.38/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.58          | (v1_xboole_0 @ X16)
% 0.38/0.58          | ~ (l1_struct_0 @ X17)
% 0.38/0.58          | (v2_struct_0 @ X17)
% 0.38/0.58          | (v1_xboole_0 @ X18)
% 0.38/0.58          | ~ (v1_subset_1 @ X18 @ 
% 0.38/0.58               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16))))
% 0.38/0.58          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.38/0.58          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.38/0.58          | ~ (m1_subset_1 @ X18 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.38/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.38/0.58      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.58          | ~ (v1_subset_1 @ sk_B @ 
% 0.38/0.58               (u1_struct_0 @ 
% 0.38/0.58                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '47'])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      ((v1_subset_1 @ sk_B @ 
% 0.38/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['40', '52'])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['39', '53'])).
% 0.38/0.58  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['54', '55'])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['38', '56'])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['34', '57'])).
% 0.38/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf('61', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('62', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('63', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      (![X6 : $i]:
% 0.38/0.58         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf(fc4_yellow19, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @
% 0.38/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.58         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.38/0.58         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.38/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.38/0.58  thf('66', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.58          | (v1_xboole_0 @ X13)
% 0.38/0.58          | ~ (l1_struct_0 @ X14)
% 0.38/0.58          | (v2_struct_0 @ X14)
% 0.38/0.58          | (v1_xboole_0 @ X15)
% 0.38/0.58          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.38/0.58          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.38/0.58          | ~ (m1_subset_1 @ X15 @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.38/0.58          | (v4_orders_2 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('68', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.58          | (v1_xboole_0 @ X13)
% 0.38/0.58          | ~ (l1_struct_0 @ X14)
% 0.38/0.58          | (v2_struct_0 @ X14)
% 0.38/0.58          | (v1_xboole_0 @ X15)
% 0.38/0.58          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.38/0.58          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.38/0.58          | ~ (m1_subset_1 @ X15 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.38/0.58          | (v4_orders_2 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.38/0.58      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['65', '70'])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('74', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.38/0.58  thf('75', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['64', '74'])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['63', '75'])).
% 0.38/0.58  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('78', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.58  thf('79', plain,
% 0.38/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['62', '78'])).
% 0.38/0.58  thf('80', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['61', '79'])).
% 0.38/0.58  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('82', plain,
% 0.38/0.58      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['80', '81'])).
% 0.38/0.58  thf('83', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('84', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('85', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      (![X6 : $i]:
% 0.38/0.58         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.58  thf('87', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf(dt_k3_yellow19, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @
% 0.38/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.38/0.58         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.38/0.58  thf('88', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.58          | (v1_xboole_0 @ X10)
% 0.38/0.58          | ~ (l1_struct_0 @ X11)
% 0.38/0.58          | (v2_struct_0 @ X11)
% 0.38/0.58          | (v1_xboole_0 @ X12)
% 0.38/0.58          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.38/0.58          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.38/0.58          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.38/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12) @ X11))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.38/0.58  thf('89', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('90', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('91', plain,
% 0.38/0.58      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.58  thf('92', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.58          | (v1_xboole_0 @ X10)
% 0.38/0.58          | ~ (l1_struct_0 @ X11)
% 0.38/0.58          | (v2_struct_0 @ X11)
% 0.38/0.58          | (v1_xboole_0 @ X12)
% 0.38/0.58          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.58          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.58          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.38/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12) @ X11))),
% 0.38/0.58      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.38/0.58  thf('93', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['87', '92'])).
% 0.38/0.58  thf('94', plain,
% 0.38/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('95', plain,
% 0.38/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('96', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.38/0.58  thf('97', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.58             X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['86', '96'])).
% 0.38/0.58  thf('98', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.58             X0)
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['85', '97'])).
% 0.38/0.58  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('100', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.58          | (v1_xboole_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (l1_struct_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['98', '99'])).
% 0.38/0.58  thf('101', plain,
% 0.38/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.58           sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['84', '100'])).
% 0.38/0.58  thf('102', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.58           sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['83', '101'])).
% 0.38/0.58  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('104', plain,
% 0.38/0.58      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.58         sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['102', '103'])).
% 0.38/0.58  thf('105', plain,
% 0.38/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.58        | (r3_waybel_9 @ sk_A @ 
% 0.38/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('106', plain,
% 0.38/0.58      (((r3_waybel_9 @ sk_A @ 
% 0.38/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.38/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.58      inference('split', [status(esa)], ['105'])).
% 0.38/0.58  thf('107', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t12_yellow19, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.38/0.58             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.38/0.58                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.38/0.58  thf('108', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X19)
% 0.38/0.58          | ~ (v4_orders_2 @ X19)
% 0.38/0.58          | ~ (v7_waybel_0 @ X19)
% 0.38/0.58          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.38/0.58          | ~ (r3_waybel_9 @ X20 @ X19 @ X21)
% 0.38/0.58          | (r1_waybel_7 @ X20 @ (k2_yellow19 @ X20 @ X19) @ X21)
% 0.38/0.58          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.38/0.58          | ~ (l1_pre_topc @ X20)
% 0.38/0.58          | ~ (v2_pre_topc @ X20)
% 0.38/0.58          | (v2_struct_0 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.38/0.58  thf('109', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_A)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.38/0.59          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.38/0.59          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.38/0.59          | ~ (v7_waybel_0 @ X0)
% 0.38/0.59          | ~ (v4_orders_2 @ X0)
% 0.38/0.59          | (v2_struct_0 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['107', '108'])).
% 0.38/0.59  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('112', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.38/0.59          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.38/0.59          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.38/0.59          | ~ (v7_waybel_0 @ X0)
% 0.38/0.59          | ~ (v4_orders_2 @ X0)
% 0.38/0.59          | (v2_struct_0 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.38/0.59  thf('113', plain,
% 0.38/0.59      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | ~ (l1_waybel_0 @ 
% 0.38/0.59              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59            (k2_yellow19 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59            sk_C)
% 0.38/0.59         | (v2_struct_0 @ sk_A)))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['106', '112'])).
% 0.38/0.59  thf('114', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59            (k2_yellow19 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59            sk_C)
% 0.38/0.59         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['104', '113'])).
% 0.38/0.59  thf('115', plain,
% 0.38/0.59      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59            (k2_yellow19 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59            sk_C)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['114'])).
% 0.38/0.59  thf('116', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59            (k2_yellow19 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59            sk_C)
% 0.38/0.59         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['82', '115'])).
% 0.38/0.59  thf('117', plain,
% 0.38/0.59      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59            (k2_yellow19 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59            sk_C)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['116'])).
% 0.38/0.59  thf('118', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59            (k2_yellow19 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59            sk_C)
% 0.38/0.59         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['60', '117'])).
% 0.38/0.59  thf('119', plain,
% 0.38/0.59      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59            (k2_yellow19 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.59            sk_C)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['118'])).
% 0.38/0.59  thf('120', plain,
% 0.38/0.59      ((((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['33', '119'])).
% 0.38/0.59  thf('121', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.59  thf('122', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.59  thf('123', plain,
% 0.38/0.59      (![X6 : $i]:
% 0.38/0.59         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.59  thf('124', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ 
% 0.38/0.59        (k1_zfmisc_1 @ 
% 0.38/0.59         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('125', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.59          | (v1_xboole_0 @ X10)
% 0.38/0.59          | ~ (l1_struct_0 @ X11)
% 0.38/0.59          | (v2_struct_0 @ X11)
% 0.38/0.59          | (v1_xboole_0 @ X12)
% 0.38/0.59          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.38/0.59          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.38/0.59          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.38/0.59          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.38/0.59  thf('126', plain,
% 0.38/0.59      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.59  thf('127', plain,
% 0.38/0.59      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.59  thf('128', plain,
% 0.38/0.59      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.59  thf('129', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.59          | (v1_xboole_0 @ X10)
% 0.38/0.59          | ~ (l1_struct_0 @ X11)
% 0.38/0.59          | (v2_struct_0 @ X11)
% 0.38/0.59          | (v1_xboole_0 @ X12)
% 0.38/0.59          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.59          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.59          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59               (k1_zfmisc_1 @ 
% 0.38/0.59                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.38/0.59          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.38/0.59      inference('demod', [status(thm)], ['125', '126', '127', '128'])).
% 0.38/0.59  thf('130', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.59               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.59               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | ~ (l1_struct_0 @ X0)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['124', '129'])).
% 0.38/0.59  thf('131', plain,
% 0.38/0.59      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.59        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.59      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.59  thf('132', plain,
% 0.38/0.59      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.59        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.59  thf('133', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | ~ (l1_struct_0 @ X0)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.59      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.38/0.59  thf('134', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.59          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | ~ (l1_struct_0 @ X0)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['123', '133'])).
% 0.38/0.59  thf('135', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | ~ (l1_struct_0 @ X0)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['122', '134'])).
% 0.38/0.59  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('137', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | ~ (l1_struct_0 @ X0)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.59      inference('demod', [status(thm)], ['135', '136'])).
% 0.38/0.59  thf('138', plain,
% 0.38/0.59      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v1_xboole_0 @ sk_B)
% 0.38/0.59        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['121', '137'])).
% 0.38/0.59  thf('139', plain,
% 0.38/0.59      ((((v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['120', '138'])).
% 0.38/0.59  thf('140', plain,
% 0.38/0.59      (((~ (l1_struct_0 @ sk_A)
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['139'])).
% 0.38/0.59  thf('141', plain,
% 0.38/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '140'])).
% 0.38/0.59  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('143', plain,
% 0.38/0.59      ((((v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.38/0.59         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('demod', [status(thm)], ['141', '142'])).
% 0.38/0.59  thf('144', plain,
% 0.38/0.59      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('split', [status(esa)], ['0'])).
% 0.38/0.59  thf('145', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['143', '144'])).
% 0.38/0.59  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('147', plain,
% 0.38/0.59      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('clc', [status(thm)], ['145', '146'])).
% 0.38/0.59  thf('148', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('149', plain,
% 0.38/0.59      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('clc', [status(thm)], ['147', '148'])).
% 0.38/0.59  thf('150', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['4', '149'])).
% 0.38/0.59  thf('151', plain,
% 0.38/0.59      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '150'])).
% 0.38/0.59  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('153', plain,
% 0.38/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('demod', [status(thm)], ['151', '152'])).
% 0.38/0.59  thf(fc2_struct_0, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.59       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.59  thf('154', plain,
% 0.38/0.59      (![X8 : $i]:
% 0.38/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.38/0.59          | ~ (l1_struct_0 @ X8)
% 0.38/0.59          | (v2_struct_0 @ X8))),
% 0.38/0.59      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.59  thf('155', plain,
% 0.38/0.59      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['153', '154'])).
% 0.38/0.59  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('157', plain,
% 0.38/0.59      ((~ (l1_struct_0 @ sk_A))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('clc', [status(thm)], ['155', '156'])).
% 0.38/0.59  thf('158', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.59         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '157'])).
% 0.38/0.59  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('160', plain,
% 0.38/0.59      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.59       ~
% 0.38/0.59       ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.59      inference('demod', [status(thm)], ['158', '159'])).
% 0.38/0.59  thf('161', plain,
% 0.38/0.59      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.59       ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.59      inference('split', [status(esa)], ['105'])).
% 0.38/0.59  thf('162', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.59  thf('163', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.59  thf('164', plain,
% 0.38/0.59      (![X6 : $i]:
% 0.38/0.59         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.59  thf('165', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.59  thf('166', plain,
% 0.38/0.59      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.38/0.59         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('split', [status(esa)], ['105'])).
% 0.38/0.59  thf('167', plain,
% 0.38/0.59      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59        | (v1_xboole_0 @ sk_B)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['80', '81'])).
% 0.38/0.59  thf('168', plain,
% 0.38/0.59      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59        | (v1_xboole_0 @ sk_B)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.59  thf('169', plain,
% 0.38/0.59      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.59         sk_A)
% 0.38/0.59        | (v1_xboole_0 @ sk_B)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['102', '103'])).
% 0.38/0.59  thf('170', plain,
% 0.38/0.59      (((sk_B)
% 0.38/0.59         = (k2_yellow19 @ sk_A @ 
% 0.38/0.59            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('clc', [status(thm)], ['31', '32'])).
% 0.38/0.59  thf('171', plain,
% 0.38/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.59         ((v2_struct_0 @ X19)
% 0.38/0.59          | ~ (v4_orders_2 @ X19)
% 0.38/0.59          | ~ (v7_waybel_0 @ X19)
% 0.38/0.59          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.38/0.59          | ~ (r1_waybel_7 @ X20 @ (k2_yellow19 @ X20 @ X19) @ X21)
% 0.38/0.59          | (r3_waybel_9 @ X20 @ X19 @ X21)
% 0.38/0.59          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.38/0.59          | ~ (l1_pre_topc @ X20)
% 0.38/0.59          | ~ (v2_pre_topc @ X20)
% 0.38/0.59          | (v2_struct_0 @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.38/0.59  thf('172', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.59          | ~ (l1_waybel_0 @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.59          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['170', '171'])).
% 0.38/0.59  thf('173', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('174', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('175', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.59          | ~ (l1_waybel_0 @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.59          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['172', '173', '174'])).
% 0.38/0.59  thf('176', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['169', '175'])).
% 0.38/0.59  thf('177', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.59          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['176'])).
% 0.38/0.59  thf('178', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['168', '177'])).
% 0.38/0.59  thf('179', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.59          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['178'])).
% 0.38/0.59  thf('180', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['167', '179'])).
% 0.38/0.59  thf('181', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.59          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          | (v1_xboole_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ sk_A)
% 0.38/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['180'])).
% 0.38/0.59  thf('182', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.38/0.59         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.38/0.59         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['166', '181'])).
% 0.38/0.59  thf('183', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('184', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (r3_waybel_9 @ sk_A @ 
% 0.38/0.59            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.38/0.59         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('demod', [status(thm)], ['182', '183'])).
% 0.38/0.59  thf('185', plain,
% 0.38/0.59      ((~ (r3_waybel_9 @ sk_A @ 
% 0.38/0.59           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.59      inference('split', [status(esa)], ['0'])).
% 0.38/0.59  thf('186', plain,
% 0.38/0.59      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['184', '185'])).
% 0.38/0.59  thf('187', plain,
% 0.38/0.59      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v1_xboole_0 @ sk_B)
% 0.38/0.59        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['121', '137'])).
% 0.38/0.59  thf('188', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['186', '187'])).
% 0.38/0.59  thf('189', plain,
% 0.38/0.59      (((~ (l1_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['188'])).
% 0.38/0.59  thf('190', plain,
% 0.38/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['165', '189'])).
% 0.38/0.59  thf('191', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('192', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.59         | (v2_struct_0 @ sk_A)
% 0.38/0.59         | (v1_xboole_0 @ sk_B)))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('demod', [status(thm)], ['190', '191'])).
% 0.38/0.59  thf('193', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('194', plain,
% 0.38/0.59      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('clc', [status(thm)], ['192', '193'])).
% 0.38/0.59  thf('195', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('196', plain,
% 0.38/0.59      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('clc', [status(thm)], ['194', '195'])).
% 0.38/0.59  thf('197', plain,
% 0.38/0.59      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['164', '196'])).
% 0.38/0.59  thf('198', plain,
% 0.38/0.59      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['163', '197'])).
% 0.38/0.59  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('200', plain,
% 0.38/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('demod', [status(thm)], ['198', '199'])).
% 0.38/0.59  thf('201', plain,
% 0.38/0.59      (![X8 : $i]:
% 0.38/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.38/0.59          | ~ (l1_struct_0 @ X8)
% 0.38/0.59          | (v2_struct_0 @ X8))),
% 0.38/0.59      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.59  thf('202', plain,
% 0.38/0.59      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['200', '201'])).
% 0.38/0.59  thf('203', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('204', plain,
% 0.38/0.59      ((~ (l1_struct_0 @ sk_A))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('clc', [status(thm)], ['202', '203'])).
% 0.38/0.59  thf('205', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.59             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['162', '204'])).
% 0.38/0.59  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('207', plain,
% 0.38/0.59      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.59       ((r3_waybel_9 @ sk_A @ 
% 0.38/0.59         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.59      inference('demod', [status(thm)], ['205', '206'])).
% 0.38/0.59  thf('208', plain, ($false),
% 0.38/0.59      inference('sat_resolution*', [status(thm)], ['1', '160', '161', '207'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
