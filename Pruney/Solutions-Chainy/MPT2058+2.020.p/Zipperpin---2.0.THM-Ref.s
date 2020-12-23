%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fJQacZzlI4

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:52 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 604 expanded)
%              Number of leaves         :   38 ( 203 expanded)
%              Depth                    :   34
%              Number of atoms          : 3087 (11902 expanded)
%              Number of equality atoms :   35 ( 158 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_subset_1 @ X13 @ ( u1_struct_0 @ ( k3_yellow_1 @ X11 ) ) )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X11 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_subset_1 @ X13 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','20','23','26'])).

thf('28',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X8 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('37',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('43',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('53',plain,(
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

thf('54',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v2_waybel_0 @ X7 @ ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) )
      | ~ ( v13_waybel_0 @ X7 @ ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X6 @ X5 @ X7 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('60',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','61'])).

thf('63',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( r3_waybel_9 @ X15 @ X14 @ X16 )
      | ( r1_waybel_7 @ X15 @ ( k2_yellow19 @ X15 @ X14 ) @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['49','77'])).

thf('79',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','79'])).

thf('81',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v1_subset_1 @ X17 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) ) )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) ) ) )
      | ( X17
        = ( k2_yellow19 @ X18 @ ( k3_yellow19 @ X18 @ ( k2_struct_0 @ X18 ) @ X17 ) ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('84',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('86',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('87',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('88',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v1_subset_1 @ X17 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) ) ) )
      | ( X17
        = ( k2_yellow19 @ X18 @ ( k3_yellow19 @ X18 @ ( k2_struct_0 @ X18 ) @ X17 ) ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('91',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('92',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['80','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('105',plain,(
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

thf('106',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('107',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('108',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('109',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v2_waybel_0 @ X7 @ ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) )
      | ~ ( v13_waybel_0 @ X7 @ ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X6 @ X5 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('112',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','126'])).

thf('128',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('131',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['67'])).

thf('139',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('140',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('143',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['67'])).

thf('144',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('146',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('147',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('148',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( r1_waybel_7 @ X15 @ ( k2_yellow19 @ X15 @ X14 ) @ X16 )
      | ( r3_waybel_9 @ X15 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('149',plain,(
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
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['143','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('163',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['114'])).

thf('165',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['141','173'])).

thf('175',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','174'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('179',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','181'])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','137','138','184'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fJQacZzlI4
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 219 iterations in 0.147s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.40/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.60  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.40/0.60  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.40/0.60  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.40/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.60  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.40/0.60  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.40/0.60  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.40/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.40/0.60  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.40/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.60  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.40/0.60  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.40/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.60  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.60  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(t17_yellow19, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.60             ( v1_subset_1 @
% 0.40/0.60               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.60             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.60             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.60             ( m1_subset_1 @
% 0.40/0.60               B @ 
% 0.40/0.60               ( k1_zfmisc_1 @
% 0.40/0.60                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.60               ( ( r3_waybel_9 @
% 0.40/0.60                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.40/0.60                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.60            ( l1_pre_topc @ A ) ) =>
% 0.40/0.60          ( ![B:$i]:
% 0.40/0.60            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.60                ( v1_subset_1 @
% 0.40/0.60                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.60                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.60                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.60                ( m1_subset_1 @
% 0.40/0.60                  B @ 
% 0.40/0.60                  ( k1_zfmisc_1 @
% 0.40/0.60                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.60              ( ![C:$i]:
% 0.40/0.60                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.60                  ( ( r3_waybel_9 @
% 0.40/0.60                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.40/0.60                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.60        | ~ (r3_waybel_9 @ sk_A @ 
% 0.40/0.60             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.60       ~
% 0.40/0.60       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.60         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf(dt_l1_pre_topc, axiom,
% 0.40/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.60  thf('2', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.60  thf('3', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.60  thf(d3_struct_0, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.60  thf('5', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.60  thf('6', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.60  thf(dt_k2_struct_0, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_struct_0 @ A ) =>
% 0.40/0.60       ( m1_subset_1 @
% 0.40/0.60         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X1 : $i]:
% 0.40/0.60         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.40/0.60          | ~ (l1_struct_0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ 
% 0.40/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(d2_yellow_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf(fc5_yellow19, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.60         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.60         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.60         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.40/0.60         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.60         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.60         ( m1_subset_1 @
% 0.40/0.60           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.60       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.60         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.60         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.40/0.60          | (v1_xboole_0 @ X11)
% 0.40/0.60          | ~ (l1_struct_0 @ X12)
% 0.40/0.60          | (v2_struct_0 @ X12)
% 0.40/0.60          | (v1_xboole_0 @ X13)
% 0.40/0.60          | ~ (v1_subset_1 @ X13 @ (u1_struct_0 @ (k3_yellow_1 @ X11)))
% 0.40/0.60          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.40/0.60          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.40/0.60          | (v7_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.40/0.60      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.40/0.60          | (v1_xboole_0 @ X11)
% 0.40/0.60          | ~ (l1_struct_0 @ X12)
% 0.40/0.60          | (v2_struct_0 @ X12)
% 0.40/0.60          | (v1_xboole_0 @ X13)
% 0.40/0.60          | ~ (v1_subset_1 @ X13 @ 
% 0.40/0.60               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11))))
% 0.40/0.60          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.40/0.60          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.40/0.60          | (v7_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.40/0.60      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.60          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.60          | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.60               (u1_struct_0 @ 
% 0.40/0.60                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.60          | (v1_xboole_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (l1_struct_0 @ X0)
% 0.40/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['10', '16'])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      ((v1_subset_1 @ sk_B @ 
% 0.40/0.60        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      ((v1_subset_1 @ sk_B @ 
% 0.40/0.60        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60          | (v1_xboole_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (l1_struct_0 @ X0)
% 0.40/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '20', '23', '26'])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['7', '27'])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['28'])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['6', '29'])).
% 0.40/0.60  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.60  thf('33', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X1 : $i]:
% 0.40/0.60         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.40/0.60          | ~ (l1_struct_0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf(fc4_yellow19, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.60         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.60         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.60         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.60         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.60         ( m1_subset_1 @
% 0.40/0.60           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.60       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.60         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.60         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.60         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.40/0.60          | (v1_xboole_0 @ X8)
% 0.40/0.60          | ~ (l1_struct_0 @ X9)
% 0.40/0.60          | (v2_struct_0 @ X9)
% 0.40/0.60          | (v1_xboole_0 @ X10)
% 0.40/0.60          | ~ (v2_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.40/0.60          | ~ (v13_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.40/0.60          | ~ (m1_subset_1 @ X10 @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X8))))
% 0.40/0.60          | (v4_orders_2 @ (k3_yellow19 @ X9 @ X8 @ X10)))),
% 0.40/0.60      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.40/0.60          | (v1_xboole_0 @ X8)
% 0.40/0.60          | ~ (l1_struct_0 @ X9)
% 0.40/0.60          | (v2_struct_0 @ X9)
% 0.40/0.60          | (v1_xboole_0 @ X10)
% 0.40/0.60          | ~ (v2_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.40/0.60          | ~ (v13_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.40/0.60          | ~ (m1_subset_1 @ X10 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X8)))))
% 0.40/0.60          | (v4_orders_2 @ (k3_yellow19 @ X9 @ X8 @ X10)))),
% 0.40/0.60      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.40/0.60  thf('41', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.60          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.60          | (v1_xboole_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (l1_struct_0 @ X0)
% 0.40/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['35', '40'])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60          | (v1_xboole_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (l1_struct_0 @ X0)
% 0.40/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['34', '44'])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['45'])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['33', '46'])).
% 0.40/0.60  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.60  thf('50', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      (![X1 : $i]:
% 0.40/0.60         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.40/0.60          | ~ (l1_struct_0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf(dt_k3_yellow19, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.60         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.60         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.60         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.60         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.60         ( m1_subset_1 @
% 0.40/0.60           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.60       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.60         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.60         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.60  thf('53', plain,
% 0.40/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.40/0.60          | (v1_xboole_0 @ X5)
% 0.40/0.60          | ~ (l1_struct_0 @ X6)
% 0.40/0.60          | (v2_struct_0 @ X6)
% 0.40/0.60          | (v1_xboole_0 @ X7)
% 0.40/0.60          | ~ (v2_waybel_0 @ X7 @ (k3_yellow_1 @ X5))
% 0.40/0.60          | ~ (v13_waybel_0 @ X7 @ (k3_yellow_1 @ X5))
% 0.40/0.60          | ~ (m1_subset_1 @ X7 @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X5))))
% 0.40/0.60          | (l1_waybel_0 @ (k3_yellow19 @ X6 @ X5 @ X7) @ X6))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.40/0.60          | (v1_xboole_0 @ X5)
% 0.40/0.60          | ~ (l1_struct_0 @ X6)
% 0.40/0.60          | (v2_struct_0 @ X6)
% 0.40/0.60          | (v1_xboole_0 @ X7)
% 0.40/0.60          | ~ (v2_waybel_0 @ X7 @ (k3_lattice3 @ (k1_lattice3 @ X5)))
% 0.40/0.60          | ~ (v13_waybel_0 @ X7 @ (k3_lattice3 @ (k1_lattice3 @ X5)))
% 0.40/0.60          | ~ (m1_subset_1 @ X7 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X5)))))
% 0.40/0.60          | (l1_waybel_0 @ (k3_yellow19 @ X6 @ X5 @ X7) @ X6))),
% 0.40/0.60      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.40/0.60  thf('58', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.60          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.60          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.60          | (v1_xboole_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (l1_struct_0 @ X0)
% 0.40/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['52', '57'])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.60          | (v1_xboole_0 @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ X0)
% 0.40/0.60          | ~ (l1_struct_0 @ X0)
% 0.40/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.60           sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['51', '61'])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.60         sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['62'])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.60           sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['50', '63'])).
% 0.40/0.60  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60        | (v2_struct_0 @ sk_A)
% 0.40/0.60        | (v1_xboole_0 @ sk_B)
% 0.40/0.60        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.60           sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['64', '65'])).
% 0.40/0.60  thf('67', plain,
% 0.40/0.60      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.60        | (r3_waybel_9 @ sk_A @ 
% 0.40/0.60           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      (((r3_waybel_9 @ sk_A @ 
% 0.40/0.60         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.60         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('split', [status(esa)], ['67'])).
% 0.40/0.60  thf('69', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t12_yellow19, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.40/0.60             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.60               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.40/0.60                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.40/0.60  thf('70', plain,
% 0.40/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.60         ((v2_struct_0 @ X14)
% 0.40/0.60          | ~ (v4_orders_2 @ X14)
% 0.40/0.60          | ~ (v7_waybel_0 @ X14)
% 0.40/0.60          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.40/0.60          | ~ (r3_waybel_9 @ X15 @ X14 @ X16)
% 0.40/0.60          | (r1_waybel_7 @ X15 @ (k2_yellow19 @ X15 @ X14) @ X16)
% 0.40/0.60          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.40/0.60          | ~ (l1_pre_topc @ X15)
% 0.40/0.60          | ~ (v2_pre_topc @ X15)
% 0.40/0.60          | (v2_struct_0 @ X15))),
% 0.40/0.60      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_A)
% 0.40/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.60          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.40/0.60          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.40/0.60          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.40/0.60          | ~ (v7_waybel_0 @ X0)
% 0.40/0.60          | ~ (v4_orders_2 @ X0)
% 0.40/0.60          | (v2_struct_0 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['69', '70'])).
% 0.40/0.60  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('74', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_A)
% 0.40/0.60          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.40/0.60          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.40/0.60          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.40/0.60          | ~ (v7_waybel_0 @ X0)
% 0.40/0.60          | ~ (v4_orders_2 @ X0)
% 0.40/0.60          | (v2_struct_0 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.40/0.60  thf('75', plain,
% 0.40/0.60      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | ~ (l1_waybel_0 @ 
% 0.40/0.60              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.60         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.60            (k2_yellow19 @ sk_A @ 
% 0.40/0.60             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.60            sk_C)
% 0.40/0.60         | (v2_struct_0 @ sk_A)))
% 0.40/0.60         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['68', '74'])).
% 0.40/0.60  thf('76', plain,
% 0.40/0.60      ((((v1_xboole_0 @ sk_B)
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.60            (k2_yellow19 @ sk_A @ 
% 0.40/0.60             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.60            sk_C)
% 0.40/0.60         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.60         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['66', '75'])).
% 0.40/0.60  thf('77', plain,
% 0.40/0.60      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.60            (k2_yellow19 @ sk_A @ 
% 0.40/0.60             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.60            sk_C)
% 0.40/0.60         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (v1_xboole_0 @ sk_B)))
% 0.40/0.60         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['76'])).
% 0.40/0.60  thf('78', plain,
% 0.40/0.60      ((((v1_xboole_0 @ sk_B)
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60         | (v1_xboole_0 @ sk_B)
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.60            (k2_yellow19 @ sk_A @ 
% 0.40/0.60             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.60            sk_C)
% 0.40/0.60         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.60         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['49', '77'])).
% 0.40/0.60  thf('79', plain,
% 0.40/0.60      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.60         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.60            (k2_yellow19 @ sk_A @ 
% 0.40/0.60             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.60            sk_C)
% 0.40/0.60         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (v1_xboole_0 @ sk_B)))
% 0.40/0.60         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['78'])).
% 0.40/0.60  thf('80', plain,
% 0.40/0.60      ((((v1_xboole_0 @ sk_B)
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60         | (v1_xboole_0 @ sk_B)
% 0.40/0.60         | (v2_struct_0 @ sk_A)
% 0.40/0.60         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.60         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.60            (k2_yellow19 @ sk_A @ 
% 0.40/0.60             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.60            sk_C)
% 0.40/0.60         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.60         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['32', '79'])).
% 0.40/0.60  thf('81', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.60  thf('82', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf(t15_yellow19, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.60             ( v1_subset_1 @
% 0.40/0.60               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.60             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.60             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.60             ( m1_subset_1 @
% 0.40/0.60               B @ 
% 0.40/0.60               ( k1_zfmisc_1 @
% 0.40/0.60                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.60           ( ( B ) =
% 0.40/0.60             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.60  thf('83', plain,
% 0.40/0.60      (![X17 : $i, X18 : $i]:
% 0.40/0.60         ((v1_xboole_0 @ X17)
% 0.40/0.60          | ~ (v1_subset_1 @ X17 @ 
% 0.40/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X18))))
% 0.40/0.60          | ~ (v2_waybel_0 @ X17 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))
% 0.40/0.60          | ~ (v13_waybel_0 @ X17 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))
% 0.40/0.60          | ~ (m1_subset_1 @ X17 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))))
% 0.40/0.60          | ((X17)
% 0.40/0.60              = (k2_yellow19 @ X18 @ 
% 0.40/0.60                 (k3_yellow19 @ X18 @ (k2_struct_0 @ X18) @ X17)))
% 0.40/0.60          | ~ (l1_struct_0 @ X18)
% 0.40/0.60          | (v2_struct_0 @ X18))),
% 0.40/0.60      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.40/0.60  thf('84', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('85', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('86', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('87', plain,
% 0.40/0.60      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.60  thf('88', plain,
% 0.40/0.60      (![X17 : $i, X18 : $i]:
% 0.40/0.60         ((v1_xboole_0 @ X17)
% 0.40/0.60          | ~ (v1_subset_1 @ X17 @ 
% 0.40/0.60               (u1_struct_0 @ 
% 0.40/0.60                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18)))))
% 0.40/0.60          | ~ (v2_waybel_0 @ X17 @ 
% 0.40/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))
% 0.40/0.60          | ~ (v13_waybel_0 @ X17 @ 
% 0.40/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))
% 0.40/0.60          | ~ (m1_subset_1 @ X17 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (u1_struct_0 @ 
% 0.40/0.60                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))))
% 0.40/0.60          | ((X17)
% 0.40/0.60              = (k2_yellow19 @ X18 @ 
% 0.40/0.60                 (k3_yellow19 @ X18 @ (k2_struct_0 @ X18) @ X17)))
% 0.40/0.60          | ~ (l1_struct_0 @ X18)
% 0.40/0.60          | (v2_struct_0 @ X18))),
% 0.40/0.60      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 0.40/0.60  thf('89', plain,
% 0.40/0.60      (((v2_struct_0 @ sk_A)
% 0.40/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.60        | ((sk_B)
% 0.40/0.60            = (k2_yellow19 @ sk_A @ 
% 0.40/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.60        | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.60             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.60        | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.60             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.60        | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.60             (u1_struct_0 @ 
% 0.40/0.60              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.60        | (v1_xboole_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['82', '88'])).
% 0.40/0.60  thf('90', plain,
% 0.40/0.60      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.60  thf('91', plain,
% 0.40/0.60      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf('92', plain,
% 0.40/0.60      ((v1_subset_1 @ sk_B @ 
% 0.40/0.60        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.40/0.60  thf('93', plain,
% 0.40/0.60      (((v2_struct_0 @ sk_A)
% 0.40/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.61        | (v1_xboole_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.40/0.61  thf('94', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.61        | (v2_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['81', '93'])).
% 0.40/0.61  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('96', plain,
% 0.40/0.61      (((v1_xboole_0 @ sk_B)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.61        | (v2_struct_0 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['94', '95'])).
% 0.40/0.61  thf('97', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('98', plain,
% 0.40/0.61      (((v2_struct_0 @ sk_A)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.61      inference('clc', [status(thm)], ['96', '97'])).
% 0.40/0.61  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('100', plain,
% 0.40/0.61      (((sk_B)
% 0.40/0.61         = (k2_yellow19 @ sk_A @ 
% 0.40/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('clc', [status(thm)], ['98', '99'])).
% 0.40/0.61  thf('101', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['80', '100'])).
% 0.40/0.61  thf('102', plain,
% 0.40/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['101'])).
% 0.40/0.61  thf('103', plain,
% 0.40/0.61      (![X1 : $i]:
% 0.40/0.61         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.40/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.40/0.61          | ~ (l1_struct_0 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.61  thf('104', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.61  thf('105', plain,
% 0.40/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.40/0.61          | (v1_xboole_0 @ X5)
% 0.40/0.61          | ~ (l1_struct_0 @ X6)
% 0.40/0.61          | (v2_struct_0 @ X6)
% 0.40/0.61          | (v1_xboole_0 @ X7)
% 0.40/0.61          | ~ (v2_waybel_0 @ X7 @ (k3_yellow_1 @ X5))
% 0.40/0.61          | ~ (v13_waybel_0 @ X7 @ (k3_yellow_1 @ X5))
% 0.40/0.61          | ~ (m1_subset_1 @ X7 @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X5))))
% 0.40/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X6 @ X5 @ X7)))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.61  thf('106', plain,
% 0.40/0.61      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('107', plain,
% 0.40/0.61      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('108', plain,
% 0.40/0.61      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('109', plain,
% 0.40/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.40/0.61          | (v1_xboole_0 @ X5)
% 0.40/0.61          | ~ (l1_struct_0 @ X6)
% 0.40/0.61          | (v2_struct_0 @ X6)
% 0.40/0.61          | (v1_xboole_0 @ X7)
% 0.40/0.61          | ~ (v2_waybel_0 @ X7 @ (k3_lattice3 @ (k1_lattice3 @ X5)))
% 0.40/0.61          | ~ (v13_waybel_0 @ X7 @ (k3_lattice3 @ (k1_lattice3 @ X5)))
% 0.40/0.61          | ~ (m1_subset_1 @ X7 @ 
% 0.40/0.61               (k1_zfmisc_1 @ 
% 0.40/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X5)))))
% 0.40/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X6 @ X5 @ X7)))),
% 0.40/0.61      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.40/0.61  thf('110', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['104', '109'])).
% 0.40/0.61  thf('111', plain,
% 0.40/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.61  thf('112', plain,
% 0.40/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.61  thf('113', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.40/0.61  thf('114', plain,
% 0.40/0.61      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['103', '113'])).
% 0.40/0.61  thf('115', plain,
% 0.40/0.61      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('simplify', [status(thm)], ['114'])).
% 0.40/0.61  thf('116', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['102', '115'])).
% 0.40/0.61  thf('117', plain,
% 0.40/0.61      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['116'])).
% 0.40/0.61  thf('118', plain,
% 0.40/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['5', '117'])).
% 0.40/0.61  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('120', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['118', '119'])).
% 0.40/0.61  thf('121', plain,
% 0.40/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf('122', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['120', '121'])).
% 0.40/0.61  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('124', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['122', '123'])).
% 0.40/0.61  thf('125', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('126', plain,
% 0.40/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['124', '125'])).
% 0.40/0.61  thf('127', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['4', '126'])).
% 0.40/0.61  thf('128', plain,
% 0.40/0.61      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['3', '127'])).
% 0.40/0.61  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('130', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['128', '129'])).
% 0.40/0.61  thf(fc2_struct_0, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.61       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.61  thf('131', plain,
% 0.40/0.61      (![X3 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.40/0.61          | ~ (l1_struct_0 @ X3)
% 0.40/0.61          | (v2_struct_0 @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.61  thf('132', plain,
% 0.40/0.61      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['130', '131'])).
% 0.40/0.61  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('134', plain,
% 0.40/0.61      ((~ (l1_struct_0 @ sk_A))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['132', '133'])).
% 0.40/0.61  thf('135', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['2', '134'])).
% 0.40/0.61  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('137', plain,
% 0.40/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.61       ~
% 0.40/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.61      inference('demod', [status(thm)], ['135', '136'])).
% 0.40/0.61  thf('138', plain,
% 0.40/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.61      inference('split', [status(esa)], ['67'])).
% 0.40/0.61  thf('139', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('140', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('141', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('142', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('143', plain,
% 0.40/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.40/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('split', [status(esa)], ['67'])).
% 0.40/0.61  thf('144', plain,
% 0.40/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.61  thf('145', plain,
% 0.40/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('146', plain,
% 0.40/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.61           sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.40/0.61  thf('147', plain,
% 0.40/0.61      (((sk_B)
% 0.40/0.61         = (k2_yellow19 @ sk_A @ 
% 0.40/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('clc', [status(thm)], ['98', '99'])).
% 0.40/0.61  thf('148', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.61         ((v2_struct_0 @ X14)
% 0.40/0.61          | ~ (v4_orders_2 @ X14)
% 0.40/0.61          | ~ (v7_waybel_0 @ X14)
% 0.40/0.61          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.40/0.61          | ~ (r1_waybel_7 @ X15 @ (k2_yellow19 @ X15 @ X14) @ X16)
% 0.40/0.61          | (r3_waybel_9 @ X15 @ X14 @ X16)
% 0.40/0.61          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.40/0.61          | ~ (l1_pre_topc @ X15)
% 0.40/0.61          | ~ (v2_pre_topc @ X15)
% 0.40/0.61          | (v2_struct_0 @ X15))),
% 0.40/0.61      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.40/0.61  thf('149', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | ~ (l1_waybel_0 @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['147', '148'])).
% 0.40/0.61  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('152', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | ~ (l1_waybel_0 @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.40/0.61  thf('153', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['146', '152'])).
% 0.40/0.61  thf('154', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | (v1_xboole_0 @ sk_B))),
% 0.40/0.61      inference('simplify', [status(thm)], ['153'])).
% 0.40/0.61  thf('155', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['145', '154'])).
% 0.40/0.61  thf('156', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | (v1_xboole_0 @ sk_B))),
% 0.40/0.61      inference('simplify', [status(thm)], ['155'])).
% 0.40/0.61  thf('157', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['144', '156'])).
% 0.40/0.61  thf('158', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61          | (v2_struct_0 @ sk_A)
% 0.40/0.61          | (v1_xboole_0 @ sk_B))),
% 0.40/0.61      inference('simplify', [status(thm)], ['157'])).
% 0.40/0.61  thf('159', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.40/0.61         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['143', '158'])).
% 0.40/0.61  thf('160', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('161', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.40/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['159', '160'])).
% 0.40/0.61  thf('162', plain,
% 0.40/0.61      ((~ (r3_waybel_9 @ sk_A @ 
% 0.40/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf('163', plain,
% 0.40/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['161', '162'])).
% 0.40/0.61  thf('164', plain,
% 0.40/0.61      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('simplify', [status(thm)], ['114'])).
% 0.40/0.61  thf('165', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['163', '164'])).
% 0.40/0.61  thf('166', plain,
% 0.40/0.61      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['165'])).
% 0.40/0.61  thf('167', plain,
% 0.40/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['142', '166'])).
% 0.40/0.61  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('169', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['167', '168'])).
% 0.40/0.61  thf('170', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('171', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['169', '170'])).
% 0.40/0.61  thf('172', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('173', plain,
% 0.40/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['171', '172'])).
% 0.40/0.61  thf('174', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['141', '173'])).
% 0.40/0.61  thf('175', plain,
% 0.40/0.61      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['140', '174'])).
% 0.40/0.61  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('177', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['175', '176'])).
% 0.40/0.61  thf('178', plain,
% 0.40/0.61      (![X3 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.40/0.61          | ~ (l1_struct_0 @ X3)
% 0.40/0.61          | (v2_struct_0 @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.61  thf('179', plain,
% 0.40/0.61      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['177', '178'])).
% 0.40/0.61  thf('180', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('181', plain,
% 0.40/0.61      ((~ (l1_struct_0 @ sk_A))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['179', '180'])).
% 0.40/0.61  thf('182', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A))
% 0.40/0.61         <= (~
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['139', '181'])).
% 0.40/0.61  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('184', plain,
% 0.40/0.61      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.61      inference('demod', [status(thm)], ['182', '183'])).
% 0.40/0.61  thf('185', plain, ($false),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['1', '137', '138', '184'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
