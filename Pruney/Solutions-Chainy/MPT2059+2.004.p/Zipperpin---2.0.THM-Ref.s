%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wk6Y7K8rsA

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:53 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  342 ( 832 expanded)
%              Number of leaves         :   46 ( 278 expanded)
%              Depth                    :   42
%              Number of atoms          : 4520 (15855 expanded)
%              Number of equality atoms :   48 ( 210 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t18_yellow19,conjecture,(
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
             => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) )
              <=> ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) )).

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
               => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) )
                <=> ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow19])).

thf('0',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('20',plain,(
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

thf('21',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
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
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('28',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('40',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('49',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['26','35','44','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['10','54'])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('62',plain,(
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

thf('63',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
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
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('69',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('80',plain,(
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

thf('81',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('84',plain,(
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
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('87',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','88'])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['94'])).

thf(t13_yellow19,axiom,(
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
             => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
              <=> ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('96',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( k10_yellow_6 @ X22 @ X21 ) )
      | ( r2_waybel_7 @ X22 @ ( k2_yellow19 @ X22 @ X21 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('102',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

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

thf('103',plain,(
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

thf('104',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('105',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('106',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('107',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('108',plain,(
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
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('111',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('112',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','120'])).

thf('122',plain,
    ( ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['93','121'])).

thf('123',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['92','122'])).

thf('124',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['76','124'])).

thf('126',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['75','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['74','128'])).

thf('130',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['58','130'])).

thf('132',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['6','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('137',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('138',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('140',plain,(
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

thf('141',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('142',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('143',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('144',plain,(
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
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('147',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['138','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['137','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['136','152'])).

thf('154',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['135','153'])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['5','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('160',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','160'])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['167','168'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('170',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('171',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','178'])).

thf('180',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['94'])).

thf('188',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('189',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('190',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('191',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('192',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
   <= ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(split,[status(esa)],['94'])).

thf('193',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('194',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('195',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('196',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('197',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('198',plain,(
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
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('201',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['196','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['195','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['194','206'])).

thf('208',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','207'])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('212',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('213',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('214',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('215',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('216',plain,(
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
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('219',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('220',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['214','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['213','222'])).

thf('224',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['212','225'])).

thf('227',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','226'])).

thf('228',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('231',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('232',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('233',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('234',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('235',plain,(
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
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('238',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['233','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['232','240'])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['231','243'])).

thf('245',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['230','244'])).

thf('246',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('249',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( r2_waybel_7 @ X22 @ ( k2_yellow19 @ X22 @ X21 ) @ X23 )
      | ( r2_hidden @ X23 @ ( k10_yellow_6 @ X22 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['247','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['229','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['210','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['192','259'])).

thf('261',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('263',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('264',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['136','152'])).

thf('266',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','267'])).

thf('269',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(clc,[status(thm)],['272','273'])).

thf('275',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['190','274'])).

thf('276',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['189','275'])).

thf('277',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['276','277'])).

thf('279',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('280',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['280','281','282'])).

thf('284',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(clc,[status(thm)],['283','284'])).

thf('286',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['188','285'])).

thf('287',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('288',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['288','289','290'])).

thf('292',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['291','292'])).

thf('294',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','186','187','293'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wk6Y7K8rsA
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 204 iterations in 0.133s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.62  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.40/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.40/0.62  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.40/0.62  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.40/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.62  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.40/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.62  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.40/0.62  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.40/0.62  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.40/0.62  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.40/0.62  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.40/0.62  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.40/0.62  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.40/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.62  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.40/0.62  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.40/0.62  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.40/0.62  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.40/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.62  thf(t18_yellow19, conjecture,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.62             ( v1_subset_1 @
% 0.40/0.62               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.62             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.62             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.62             ( m1_subset_1 @
% 0.40/0.62               B @ 
% 0.40/0.62               ( k1_zfmisc_1 @
% 0.40/0.62                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.62           ( ![C:$i]:
% 0.40/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.62               ( ( r2_hidden @
% 0.40/0.62                   C @ 
% 0.40/0.62                   ( k10_yellow_6 @
% 0.40/0.62                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.40/0.62                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i]:
% 0.40/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.62            ( l1_pre_topc @ A ) ) =>
% 0.40/0.62          ( ![B:$i]:
% 0.40/0.62            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.62                ( v1_subset_1 @
% 0.40/0.62                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.62                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.62                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.62                ( m1_subset_1 @
% 0.40/0.62                  B @ 
% 0.40/0.62                  ( k1_zfmisc_1 @
% 0.40/0.62                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.62              ( ![C:$i]:
% 0.40/0.62                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.62                  ( ( r2_hidden @
% 0.40/0.62                      C @ 
% 0.40/0.62                      ( k10_yellow_6 @
% 0.40/0.62                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.40/0.62                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      ((~ (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62        | ~ (r2_hidden @ sk_C @ 
% 0.40/0.62             (k10_yellow_6 @ sk_A @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) | 
% 0.40/0.62       ~
% 0.40/0.62       ((r2_hidden @ sk_C @ 
% 0.40/0.62         (k10_yellow_6 @ sk_A @ 
% 0.40/0.62          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf(d1_xboole_0, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.62  thf(dt_l1_pre_topc, axiom,
% 0.40/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.62  thf('3', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf(d3_struct_0, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('5', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('6', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('7', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf(dt_k2_subset_1, axiom,
% 0.40/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.40/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.62  thf('9', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.62  thf('10', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('11', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(d2_yellow_1, axiom,
% 0.40/0.62    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62         (k1_zfmisc_1 @ 
% 0.40/0.62          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.62      inference('sup+', [status(thm)], ['12', '15'])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62           (k1_zfmisc_1 @ 
% 0.40/0.62            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['11', '16'])).
% 0.40/0.62  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.62  thf(fc5_yellow19, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.62         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.62         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.62         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.40/0.62         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.62         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.62         ( m1_subset_1 @
% 0.40/0.62           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.62       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.62         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.62         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.40/0.62          | (v1_xboole_0 @ X18)
% 0.40/0.62          | ~ (l1_struct_0 @ X19)
% 0.40/0.62          | (v2_struct_0 @ X19)
% 0.40/0.62          | (v1_xboole_0 @ X20)
% 0.40/0.62          | ~ (v1_subset_1 @ X20 @ (u1_struct_0 @ (k3_yellow_1 @ X18)))
% 0.40/0.62          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.40/0.62          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.40/0.62          | ~ (m1_subset_1 @ X20 @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X18))))
% 0.40/0.62          | (v7_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.40/0.62      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.40/0.62          | (v1_xboole_0 @ X18)
% 0.40/0.62          | ~ (l1_struct_0 @ X19)
% 0.40/0.62          | (v2_struct_0 @ X19)
% 0.40/0.62          | (v1_xboole_0 @ X20)
% 0.40/0.62          | ~ (v1_subset_1 @ X20 @ 
% 0.40/0.62               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18))))
% 0.40/0.62          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.40/0.62          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.40/0.62          | ~ (m1_subset_1 @ X20 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 0.40/0.62          | (v7_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62               (u1_struct_0 @ 
% 0.40/0.62                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['19', '25'])).
% 0.40/0.62  thf('27', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('32', plain,
% 0.40/0.62      (((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.62      inference('sup+', [status(thm)], ['28', '31'])).
% 0.40/0.62  thf('33', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['27', '32'])).
% 0.40/0.62  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.40/0.62  thf('36', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('37', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('38', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('39', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('40', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      (((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.62      inference('sup+', [status(thm)], ['37', '40'])).
% 0.40/0.62  thf('42', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['36', '41'])).
% 0.40/0.62  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('44', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.62  thf('45', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('46', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('47', plain,
% 0.40/0.62      ((v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('48', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('49', plain,
% 0.40/0.62      ((v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.62  thf('50', plain,
% 0.40/0.62      (((v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.62      inference('sup+', [status(thm)], ['46', '49'])).
% 0.40/0.62  thf('51', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['45', '50'])).
% 0.40/0.62  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('53', plain,
% 0.40/0.62      ((v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.40/0.62  thf('54', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['26', '35', '44', '53'])).
% 0.40/0.62  thf('55', plain,
% 0.40/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['10', '54'])).
% 0.40/0.62  thf('56', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['7', '55'])).
% 0.40/0.62  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('58', plain,
% 0.40/0.62      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.40/0.62  thf('59', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('60', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('61', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.62  thf(fc4_yellow19, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.62         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.62         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.62         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.62         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.62         ( m1_subset_1 @
% 0.40/0.62           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.62       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.62         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.62         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.62         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.62  thf('62', plain,
% 0.40/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.62          | (v1_xboole_0 @ X15)
% 0.40/0.62          | ~ (l1_struct_0 @ X16)
% 0.40/0.62          | (v2_struct_0 @ X16)
% 0.40/0.62          | (v1_xboole_0 @ X17)
% 0.40/0.62          | ~ (v2_waybel_0 @ X17 @ (k3_yellow_1 @ X15))
% 0.40/0.62          | ~ (v13_waybel_0 @ X17 @ (k3_yellow_1 @ X15))
% 0.40/0.62          | ~ (m1_subset_1 @ X17 @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X15))))
% 0.40/0.62          | (v4_orders_2 @ (k3_yellow19 @ X16 @ X15 @ X17)))),
% 0.40/0.62      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.40/0.62  thf('63', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('64', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('65', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('66', plain,
% 0.40/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.62          | (v1_xboole_0 @ X15)
% 0.40/0.62          | ~ (l1_struct_0 @ X16)
% 0.40/0.62          | (v2_struct_0 @ X16)
% 0.40/0.62          | (v1_xboole_0 @ X17)
% 0.40/0.62          | ~ (v2_waybel_0 @ X17 @ (k3_lattice3 @ (k1_lattice3 @ X15)))
% 0.40/0.62          | ~ (v13_waybel_0 @ X17 @ (k3_lattice3 @ (k1_lattice3 @ X15)))
% 0.40/0.62          | ~ (m1_subset_1 @ X17 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X15)))))
% 0.40/0.62          | (v4_orders_2 @ (k3_yellow19 @ X16 @ X15 @ X17)))),
% 0.40/0.62      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.40/0.62  thf('67', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['61', '66'])).
% 0.40/0.62  thf('68', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.40/0.62  thf('69', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.62  thf('70', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.40/0.62  thf('71', plain,
% 0.40/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['60', '70'])).
% 0.40/0.62  thf('72', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['59', '71'])).
% 0.40/0.62  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('74', plain,
% 0.40/0.62      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['72', '73'])).
% 0.40/0.62  thf('75', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('76', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('77', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('78', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('79', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.62  thf(dt_k3_yellow19, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.62         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.62         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.62         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.62         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.62         ( m1_subset_1 @
% 0.40/0.62           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.62       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.62         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.62         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.62  thf('80', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.62          | (v1_xboole_0 @ X12)
% 0.40/0.62          | ~ (l1_struct_0 @ X13)
% 0.40/0.62          | (v2_struct_0 @ X13)
% 0.40/0.62          | (v1_xboole_0 @ X14)
% 0.40/0.62          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.62          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.40/0.62          | (l1_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14) @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.62  thf('81', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('82', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('83', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('84', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.62          | (v1_xboole_0 @ X12)
% 0.40/0.62          | ~ (l1_struct_0 @ X13)
% 0.40/0.62          | (v2_struct_0 @ X13)
% 0.40/0.62          | (v1_xboole_0 @ X14)
% 0.40/0.62          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.62          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.40/0.62          | (l1_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14) @ X13))),
% 0.40/0.62      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.40/0.62  thf('85', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.40/0.62           X0)
% 0.40/0.62          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['79', '84'])).
% 0.40/0.62  thf('86', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.40/0.62  thf('87', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.62  thf('88', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.40/0.62           X0)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.40/0.62  thf('89', plain,
% 0.40/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (l1_waybel_0 @ 
% 0.40/0.62           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['78', '88'])).
% 0.40/0.62  thf('90', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (l1_waybel_0 @ 
% 0.40/0.62           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['77', '89'])).
% 0.40/0.62  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('92', plain,
% 0.40/0.62      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.40/0.62         sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['90', '91'])).
% 0.40/0.62  thf('93', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('94', plain,
% 0.40/0.62      (((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62        | (r2_hidden @ sk_C @ 
% 0.40/0.62           (k10_yellow_6 @ sk_A @ 
% 0.40/0.62            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('95', plain,
% 0.40/0.62      (((r2_hidden @ sk_C @ 
% 0.40/0.62         (k10_yellow_6 @ sk_A @ 
% 0.40/0.62          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('split', [status(esa)], ['94'])).
% 0.40/0.62  thf(t13_yellow19, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.40/0.62             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.40/0.62           ( ![C:$i]:
% 0.40/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.62               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) <=>
% 0.40/0.62                 ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.40/0.62  thf('96', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         ((v2_struct_0 @ X21)
% 0.40/0.62          | ~ (v4_orders_2 @ X21)
% 0.40/0.62          | ~ (v7_waybel_0 @ X21)
% 0.40/0.62          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.40/0.62          | ~ (r2_hidden @ X23 @ (k10_yellow_6 @ X22 @ X21))
% 0.40/0.62          | (r2_waybel_7 @ X22 @ (k2_yellow19 @ X22 @ X21) @ X23)
% 0.40/0.62          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.40/0.62          | ~ (l1_pre_topc @ X22)
% 0.40/0.62          | ~ (v2_pre_topc @ X22)
% 0.40/0.62          | (v2_struct_0 @ X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.40/0.62  thf('97', plain,
% 0.40/0.62      ((((v2_struct_0 @ sk_A)
% 0.40/0.62         | ~ (v2_pre_topc @ sk_A)
% 0.40/0.62         | ~ (l1_pre_topc @ sk_A)
% 0.40/0.62         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ 
% 0.40/0.62            (k2_yellow19 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.40/0.62            sk_C)
% 0.40/0.62         | ~ (l1_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (v4_orders_2 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['95', '96'])).
% 0.40/0.62  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('100', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('101', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('102', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf(t15_yellow19, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.62             ( v1_subset_1 @
% 0.40/0.62               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.62             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.62             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.62             ( m1_subset_1 @
% 0.40/0.62               B @ 
% 0.40/0.62               ( k1_zfmisc_1 @
% 0.40/0.62                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.62           ( ( B ) =
% 0.40/0.62             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.62  thf('103', plain,
% 0.40/0.62      (![X24 : $i, X25 : $i]:
% 0.40/0.62         ((v1_xboole_0 @ X24)
% 0.40/0.62          | ~ (v1_subset_1 @ X24 @ 
% 0.40/0.62               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X25))))
% 0.40/0.62          | ~ (v2_waybel_0 @ X24 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))
% 0.40/0.62          | ~ (v13_waybel_0 @ X24 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))
% 0.40/0.62          | ~ (m1_subset_1 @ X24 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))))
% 0.40/0.62          | ((X24)
% 0.40/0.62              = (k2_yellow19 @ X25 @ 
% 0.40/0.62                 (k3_yellow19 @ X25 @ (k2_struct_0 @ X25) @ X24)))
% 0.40/0.62          | ~ (l1_struct_0 @ X25)
% 0.40/0.62          | (v2_struct_0 @ X25))),
% 0.40/0.62      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.40/0.62  thf('104', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('105', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('106', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('107', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('108', plain,
% 0.40/0.62      (![X24 : $i, X25 : $i]:
% 0.40/0.62         ((v1_xboole_0 @ X24)
% 0.40/0.62          | ~ (v1_subset_1 @ X24 @ 
% 0.40/0.62               (u1_struct_0 @ 
% 0.40/0.62                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25)))))
% 0.40/0.62          | ~ (v2_waybel_0 @ X24 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))
% 0.40/0.62          | ~ (v13_waybel_0 @ X24 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))
% 0.40/0.62          | ~ (m1_subset_1 @ X24 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ 
% 0.40/0.62                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))))
% 0.40/0.62          | ((X24)
% 0.40/0.62              = (k2_yellow19 @ X25 @ 
% 0.40/0.62                 (k3_yellow19 @ X25 @ (k2_struct_0 @ X25) @ X24)))
% 0.40/0.62          | ~ (l1_struct_0 @ X25)
% 0.40/0.62          | (v2_struct_0 @ X25))),
% 0.40/0.62      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.40/0.62  thf('109', plain,
% 0.40/0.62      (((v2_struct_0 @ sk_A)
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | ((sk_B_2)
% 0.40/0.62            = (k2_yellow19 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62        | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62             (u1_struct_0 @ 
% 0.40/0.62              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2))),
% 0.40/0.62      inference('sup-', [status(thm)], ['102', '108'])).
% 0.40/0.62  thf('110', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('111', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('112', plain,
% 0.40/0.62      ((v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.62  thf('113', plain,
% 0.40/0.62      (((v2_struct_0 @ sk_A)
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | ((sk_B_2)
% 0.40/0.62            = (k2_yellow19 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2))),
% 0.40/0.62      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.40/0.62  thf('114', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | ((sk_B_2)
% 0.40/0.62            = (k2_yellow19 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62        | (v2_struct_0 @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['101', '113'])).
% 0.40/0.62  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('116', plain,
% 0.40/0.62      (((v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | ((sk_B_2)
% 0.40/0.62            = (k2_yellow19 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62        | (v2_struct_0 @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['114', '115'])).
% 0.40/0.62  thf('117', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('118', plain,
% 0.40/0.62      (((v2_struct_0 @ sk_A)
% 0.40/0.62        | ((sk_B_2)
% 0.40/0.62            = (k2_yellow19 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.40/0.62      inference('clc', [status(thm)], ['116', '117'])).
% 0.40/0.62  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('120', plain,
% 0.40/0.62      (((sk_B_2)
% 0.40/0.62         = (k2_yellow19 @ sk_A @ 
% 0.40/0.62            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('clc', [status(thm)], ['118', '119'])).
% 0.40/0.62  thf('121', plain,
% 0.40/0.62      ((((v2_struct_0 @ sk_A)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | ~ (l1_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (v4_orders_2 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['97', '98', '99', '100', '120'])).
% 0.40/0.62  thf('122', plain,
% 0.40/0.62      (((~ (l1_waybel_0 @ 
% 0.40/0.62            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (v4_orders_2 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v2_struct_0 @ sk_A)))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['93', '121'])).
% 0.40/0.62  thf('123', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (v4_orders_2 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['92', '122'])).
% 0.40/0.62  thf('124', plain,
% 0.40/0.62      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (v4_orders_2 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['123'])).
% 0.40/0.62  thf('125', plain,
% 0.40/0.62      (((~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['76', '124'])).
% 0.40/0.62  thf('126', plain,
% 0.40/0.62      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | ~ (v4_orders_2 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['125'])).
% 0.40/0.62  thf('127', plain,
% 0.40/0.62      (((~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | ~ (v4_orders_2 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['75', '126'])).
% 0.40/0.62  thf('128', plain,
% 0.40/0.62      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | ~ (v4_orders_2 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['127'])).
% 0.40/0.62  thf('129', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['74', '128'])).
% 0.40/0.62  thf('130', plain,
% 0.40/0.62      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | ~ (v7_waybel_0 @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['129'])).
% 0.40/0.62  thf('131', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['58', '130'])).
% 0.40/0.62  thf('132', plain,
% 0.40/0.62      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['131'])).
% 0.40/0.62  thf('133', plain,
% 0.40/0.62      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '132'])).
% 0.40/0.62  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('135', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['133', '134'])).
% 0.40/0.62  thf('136', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('137', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('138', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('139', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('140', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.62          | (v1_xboole_0 @ X12)
% 0.40/0.62          | ~ (l1_struct_0 @ X13)
% 0.40/0.62          | (v2_struct_0 @ X13)
% 0.40/0.62          | (v1_xboole_0 @ X14)
% 0.40/0.62          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.62          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.40/0.62          | ~ (v2_struct_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.62  thf('141', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('142', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('143', plain,
% 0.40/0.62      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.62  thf('144', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.62          | (v1_xboole_0 @ X12)
% 0.40/0.62          | ~ (l1_struct_0 @ X13)
% 0.40/0.62          | (v2_struct_0 @ X13)
% 0.40/0.62          | (v1_xboole_0 @ X14)
% 0.40/0.62          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.62          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.40/0.62          | ~ (v2_struct_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.40/0.62      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.40/0.62  thf('145', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['139', '144'])).
% 0.40/0.62  thf('146', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('147', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('148', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.40/0.62  thf('149', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.40/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['138', '148'])).
% 0.40/0.62  thf('150', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ sk_A)
% 0.40/0.62          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['137', '149'])).
% 0.40/0.62  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('152', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['150', '151'])).
% 0.40/0.62  thf('153', plain,
% 0.40/0.62      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['136', '152'])).
% 0.40/0.62  thf('154', plain,
% 0.40/0.62      ((((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['135', '153'])).
% 0.40/0.62  thf('155', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['154'])).
% 0.40/0.62  thf('156', plain,
% 0.40/0.62      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.62         | (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['5', '155'])).
% 0.40/0.62  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('158', plain,
% 0.40/0.62      ((((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62         <= (((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['156', '157'])).
% 0.40/0.62  thf('159', plain,
% 0.40/0.62      ((~ (r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf('160', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['158', '159'])).
% 0.40/0.62  thf('161', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup+', [status(thm)], ['4', '160'])).
% 0.40/0.62  thf('162', plain,
% 0.40/0.62      ((((v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['161'])).
% 0.40/0.62  thf('163', plain,
% 0.40/0.62      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '162'])).
% 0.40/0.62  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('165', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62         | (v2_struct_0 @ sk_A)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['163', '164'])).
% 0.40/0.62  thf('166', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('167', plain,
% 0.40/0.62      ((((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('clc', [status(thm)], ['165', '166'])).
% 0.40/0.62  thf('168', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('169', plain,
% 0.40/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('clc', [status(thm)], ['167', '168'])).
% 0.40/0.62  thf(rc7_pre_topc, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.62       ( ?[B:$i]:
% 0.40/0.62         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.62           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.40/0.62  thf('170', plain,
% 0.40/0.62      (![X10 : $i]:
% 0.40/0.62         ((m1_subset_1 @ (sk_B_1 @ X10) @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.40/0.62          | ~ (l1_pre_topc @ X10)
% 0.40/0.62          | ~ (v2_pre_topc @ X10)
% 0.40/0.62          | (v2_struct_0 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.40/0.62  thf(t5_subset, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.40/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.40/0.62  thf('171', plain,
% 0.40/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X5 @ X6)
% 0.40/0.62          | ~ (v1_xboole_0 @ X7)
% 0.40/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.40/0.62  thf('172', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((v2_struct_0 @ X0)
% 0.40/0.62          | ~ (v2_pre_topc @ X0)
% 0.40/0.62          | ~ (l1_pre_topc @ X0)
% 0.40/0.62          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.40/0.62          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['170', '171'])).
% 0.40/0.62  thf('173', plain,
% 0.40/0.62      ((![X0 : $i]:
% 0.40/0.62          (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 0.40/0.62           | ~ (l1_pre_topc @ sk_A)
% 0.40/0.62           | ~ (v2_pre_topc @ sk_A)
% 0.40/0.62           | (v2_struct_0 @ sk_A)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['169', '172'])).
% 0.40/0.62  thf('174', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('175', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('176', plain,
% 0.40/0.62      ((![X0 : $i]:
% 0.40/0.62          (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['173', '174', '175'])).
% 0.40/0.62  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('178', plain,
% 0.40/0.62      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('clc', [status(thm)], ['176', '177'])).
% 0.40/0.62  thf('179', plain,
% 0.40/0.62      (((v1_xboole_0 @ (sk_B_1 @ sk_A)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['2', '178'])).
% 0.40/0.62  thf('180', plain,
% 0.40/0.62      (![X10 : $i]:
% 0.40/0.62         (~ (v1_xboole_0 @ (sk_B_1 @ X10))
% 0.40/0.62          | ~ (l1_pre_topc @ X10)
% 0.40/0.62          | ~ (v2_pre_topc @ X10)
% 0.40/0.62          | (v2_struct_0 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.40/0.62  thf('181', plain,
% 0.40/0.62      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['179', '180'])).
% 0.40/0.62  thf('182', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('184', plain,
% 0.40/0.62      (((v2_struct_0 @ sk_A))
% 0.40/0.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.40/0.62             ((r2_hidden @ sk_C @ 
% 0.40/0.62               (k10_yellow_6 @ sk_A @ 
% 0.40/0.62                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['181', '182', '183'])).
% 0.40/0.62  thf('185', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('186', plain,
% 0.40/0.62      (((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) | 
% 0.40/0.62       ~
% 0.40/0.62       ((r2_hidden @ sk_C @ 
% 0.40/0.62         (k10_yellow_6 @ sk_A @ 
% 0.40/0.62          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['184', '185'])).
% 0.40/0.62  thf('187', plain,
% 0.40/0.62      (((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) | 
% 0.40/0.62       ((r2_hidden @ sk_C @ 
% 0.40/0.62         (k10_yellow_6 @ sk_A @ 
% 0.40/0.62          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.40/0.62      inference('split', [status(esa)], ['94'])).
% 0.40/0.62  thf('188', plain,
% 0.40/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.62  thf('189', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('190', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('191', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('192', plain,
% 0.40/0.62      (((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C))
% 0.40/0.62         <= (((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.62      inference('split', [status(esa)], ['94'])).
% 0.40/0.62  thf('193', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('194', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('195', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('196', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('197', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('198', plain,
% 0.40/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.62          | (v1_xboole_0 @ X15)
% 0.40/0.62          | ~ (l1_struct_0 @ X16)
% 0.40/0.62          | (v2_struct_0 @ X16)
% 0.40/0.62          | (v1_xboole_0 @ X17)
% 0.40/0.62          | ~ (v2_waybel_0 @ X17 @ (k3_lattice3 @ (k1_lattice3 @ X15)))
% 0.40/0.62          | ~ (v13_waybel_0 @ X17 @ (k3_lattice3 @ (k1_lattice3 @ X15)))
% 0.40/0.62          | ~ (m1_subset_1 @ X17 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X15)))))
% 0.40/0.62          | (v4_orders_2 @ (k3_yellow19 @ X16 @ X15 @ X17)))),
% 0.40/0.62      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.40/0.62  thf('199', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['197', '198'])).
% 0.40/0.62  thf('200', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('201', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('202', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['199', '200', '201'])).
% 0.40/0.62  thf('203', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.40/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['196', '202'])).
% 0.40/0.62  thf('204', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ sk_A)
% 0.40/0.62          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['195', '203'])).
% 0.40/0.62  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('206', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['204', '205'])).
% 0.40/0.62  thf('207', plain,
% 0.40/0.62      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['194', '206'])).
% 0.40/0.62  thf('208', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['193', '207'])).
% 0.40/0.62  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('210', plain,
% 0.40/0.62      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['208', '209'])).
% 0.40/0.62  thf('211', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('212', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('213', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('214', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('215', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('216', plain,
% 0.40/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.40/0.62          | (v1_xboole_0 @ X18)
% 0.40/0.62          | ~ (l1_struct_0 @ X19)
% 0.40/0.62          | (v2_struct_0 @ X19)
% 0.40/0.62          | (v1_xboole_0 @ X20)
% 0.40/0.62          | ~ (v1_subset_1 @ X20 @ 
% 0.40/0.62               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18))))
% 0.40/0.62          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.40/0.62          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.40/0.62          | ~ (m1_subset_1 @ X20 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 0.40/0.62          | (v7_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.40/0.62  thf('217', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62               (u1_struct_0 @ 
% 0.40/0.62                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['215', '216'])).
% 0.40/0.62  thf('218', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('219', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('220', plain,
% 0.40/0.62      ((v1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.62  thf('221', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 0.40/0.62  thf('222', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.40/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['214', '221'])).
% 0.40/0.62  thf('223', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ sk_A)
% 0.40/0.62          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['213', '222'])).
% 0.40/0.62  thf('224', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('225', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['223', '224'])).
% 0.40/0.62  thf('226', plain,
% 0.40/0.62      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['212', '225'])).
% 0.40/0.62  thf('227', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['211', '226'])).
% 0.40/0.62  thf('228', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('229', plain,
% 0.40/0.62      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['227', '228'])).
% 0.40/0.62  thf('230', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('231', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.40/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('232', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('233', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('234', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('235', plain,
% 0.40/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.62          | (v1_xboole_0 @ X12)
% 0.40/0.62          | ~ (l1_struct_0 @ X13)
% 0.40/0.62          | (v2_struct_0 @ X13)
% 0.40/0.62          | (v1_xboole_0 @ X14)
% 0.40/0.62          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.62          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.40/0.62          | (l1_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14) @ X13))),
% 0.40/0.62      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.40/0.62  thf('236', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.40/0.62           X0)
% 0.40/0.62          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['234', '235'])).
% 0.40/0.62  thf('237', plain,
% 0.40/0.62      ((v13_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('238', plain,
% 0.40/0.62      ((v2_waybel_0 @ sk_B_2 @ 
% 0.40/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.62  thf('239', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.40/0.62           X0)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['236', '237', '238'])).
% 0.40/0.62  thf('240', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.40/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (l1_waybel_0 @ 
% 0.40/0.62             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['233', '239'])).
% 0.40/0.62  thf('241', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ sk_A)
% 0.40/0.62          | (l1_waybel_0 @ 
% 0.40/0.62             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['232', '240'])).
% 0.40/0.62  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('243', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.40/0.62           X0)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.62      inference('demod', [status(thm)], ['241', '242'])).
% 0.40/0.62  thf('244', plain,
% 0.40/0.62      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (l1_waybel_0 @ 
% 0.40/0.62           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['231', '243'])).
% 0.40/0.62  thf('245', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | (l1_waybel_0 @ 
% 0.40/0.62           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['230', '244'])).
% 0.40/0.62  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('247', plain,
% 0.40/0.62      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.40/0.62         sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['245', '246'])).
% 0.40/0.62  thf('248', plain,
% 0.40/0.62      (((sk_B_2)
% 0.40/0.62         = (k2_yellow19 @ sk_A @ 
% 0.40/0.62            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('clc', [status(thm)], ['118', '119'])).
% 0.40/0.62  thf('249', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         ((v2_struct_0 @ X21)
% 0.40/0.62          | ~ (v4_orders_2 @ X21)
% 0.40/0.62          | ~ (v7_waybel_0 @ X21)
% 0.40/0.62          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.40/0.62          | ~ (r2_waybel_7 @ X22 @ (k2_yellow19 @ X22 @ X21) @ X23)
% 0.40/0.62          | (r2_hidden @ X23 @ (k10_yellow_6 @ X22 @ X21))
% 0.40/0.62          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.40/0.62          | ~ (l1_pre_topc @ X22)
% 0.40/0.62          | ~ (v2_pre_topc @ X22)
% 0.40/0.62          | (v2_struct_0 @ X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.40/0.62  thf('250', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r2_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r2_hidden @ X0 @ 
% 0.40/0.62             (k10_yellow_6 @ sk_A @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62          | ~ (l1_waybel_0 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.40/0.62          | ~ (v7_waybel_0 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v4_orders_2 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['248', '249'])).
% 0.40/0.62  thf('251', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('252', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('253', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r2_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r2_hidden @ X0 @ 
% 0.40/0.62             (k10_yellow_6 @ sk_A @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62          | ~ (l1_waybel_0 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.40/0.62          | ~ (v7_waybel_0 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v4_orders_2 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.62      inference('demod', [status(thm)], ['250', '251', '252'])).
% 0.40/0.62  thf('254', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v4_orders_2 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v7_waybel_0 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (r2_hidden @ X0 @ 
% 0.40/0.62             (k10_yellow_6 @ sk_A @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | ~ (r2_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['247', '253'])).
% 0.40/0.62  thf('255', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r2_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r2_hidden @ X0 @ 
% 0.40/0.62             (k10_yellow_6 @ sk_A @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62          | ~ (v7_waybel_0 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v4_orders_2 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['254'])).
% 0.40/0.62  thf('256', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | ~ (v4_orders_2 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (r2_hidden @ X0 @ 
% 0.40/0.62             (k10_yellow_6 @ sk_A @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (r2_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['229', '255'])).
% 0.40/0.62  thf('257', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r2_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r2_hidden @ X0 @ 
% 0.40/0.62             (k10_yellow_6 @ sk_A @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62          | ~ (v4_orders_2 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['256'])).
% 0.40/0.62  thf('258', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.62          | (r2_hidden @ X0 @ 
% 0.40/0.62             (k10_yellow_6 @ sk_A @ 
% 0.40/0.62              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['210', '257'])).
% 0.40/0.63  thf('259', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (r2_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63          | (r2_hidden @ X0 @ 
% 0.40/0.63             (k10_yellow_6 @ sk_A @ 
% 0.40/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.63          | (v1_xboole_0 @ sk_B_2)
% 0.40/0.63          | (v2_struct_0 @ sk_A)
% 0.40/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['258'])).
% 0.40/0.63  thf('260', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.63         | (r2_hidden @ sk_C @ 
% 0.40/0.63            (k10_yellow_6 @ sk_A @ 
% 0.40/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.40/0.63         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.40/0.63         <= (((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['192', '259'])).
% 0.40/0.63  thf('261', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('262', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.63         | (r2_hidden @ sk_C @ 
% 0.40/0.63            (k10_yellow_6 @ sk_A @ 
% 0.40/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))
% 0.40/0.63         <= (((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('demod', [status(thm)], ['260', '261'])).
% 0.40/0.63  thf('263', plain,
% 0.40/0.63      ((~ (r2_hidden @ sk_C @ 
% 0.40/0.63           (k10_yellow_6 @ sk_A @ 
% 0.40/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))))),
% 0.40/0.63      inference('split', [status(esa)], ['0'])).
% 0.40/0.63  thf('264', plain,
% 0.40/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.40/0.63         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['262', '263'])).
% 0.40/0.63  thf('265', plain,
% 0.40/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B_2)
% 0.40/0.63        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['136', '152'])).
% 0.40/0.63  thf('266', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.63         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['264', '265'])).
% 0.40/0.63  thf('267', plain,
% 0.40/0.63      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B_2)
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['266'])).
% 0.40/0.63  thf('268', plain,
% 0.40/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B_2)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['191', '267'])).
% 0.40/0.63  thf('269', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('270', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B_2)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('demod', [status(thm)], ['268', '269'])).
% 0.40/0.63  thf('271', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('272', plain,
% 0.40/0.63      ((((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('clc', [status(thm)], ['270', '271'])).
% 0.40/0.63  thf('273', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('274', plain,
% 0.40/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('clc', [status(thm)], ['272', '273'])).
% 0.40/0.63  thf('275', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['190', '274'])).
% 0.40/0.63  thf('276', plain,
% 0.40/0.63      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['189', '275'])).
% 0.40/0.63  thf('277', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('278', plain,
% 0.40/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('demod', [status(thm)], ['276', '277'])).
% 0.40/0.63  thf('279', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((v2_struct_0 @ X0)
% 0.40/0.63          | ~ (v2_pre_topc @ X0)
% 0.40/0.63          | ~ (l1_pre_topc @ X0)
% 0.40/0.63          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.40/0.63          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['170', '171'])).
% 0.40/0.63  thf('280', plain,
% 0.40/0.63      ((![X0 : $i]:
% 0.40/0.63          (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 0.40/0.63           | ~ (l1_pre_topc @ sk_A)
% 0.40/0.63           | ~ (v2_pre_topc @ sk_A)
% 0.40/0.63           | (v2_struct_0 @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['278', '279'])).
% 0.40/0.63  thf('281', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('282', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('283', plain,
% 0.40/0.63      ((![X0 : $i]:
% 0.40/0.63          (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('demod', [status(thm)], ['280', '281', '282'])).
% 0.40/0.63  thf('284', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('285', plain,
% 0.40/0.63      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('clc', [status(thm)], ['283', '284'])).
% 0.40/0.63  thf('286', plain,
% 0.40/0.63      (((v1_xboole_0 @ (sk_B_1 @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['188', '285'])).
% 0.40/0.63  thf('287', plain,
% 0.40/0.63      (![X10 : $i]:
% 0.40/0.63         (~ (v1_xboole_0 @ (sk_B_1 @ X10))
% 0.40/0.63          | ~ (l1_pre_topc @ X10)
% 0.40/0.63          | ~ (v2_pre_topc @ X10)
% 0.40/0.63          | (v2_struct_0 @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.40/0.63  thf('288', plain,
% 0.40/0.63      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['286', '287'])).
% 0.40/0.63  thf('289', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('290', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('291', plain,
% 0.40/0.63      (((v2_struct_0 @ sk_A))
% 0.40/0.63         <= (~
% 0.40/0.63             ((r2_hidden @ sk_C @ 
% 0.40/0.63               (k10_yellow_6 @ sk_A @ 
% 0.40/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))) & 
% 0.40/0.63             ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.40/0.63      inference('demod', [status(thm)], ['288', '289', '290'])).
% 0.40/0.63  thf('292', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('293', plain,
% 0.40/0.63      (~ ((r2_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) | 
% 0.40/0.63       ((r2_hidden @ sk_C @ 
% 0.40/0.63         (k10_yellow_6 @ sk_A @ 
% 0.40/0.63          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['291', '292'])).
% 0.40/0.63  thf('294', plain, ($false),
% 0.40/0.63      inference('sat_resolution*', [status(thm)], ['1', '186', '187', '293'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
