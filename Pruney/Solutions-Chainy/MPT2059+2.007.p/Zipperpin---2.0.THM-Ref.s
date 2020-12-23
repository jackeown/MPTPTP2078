%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOQ8sXfqNu

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:53 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  319 ( 789 expanded)
%              Number of leaves         :   41 ( 263 expanded)
%              Depth                    :   39
%              Number of atoms          : 4302 (14801 expanded)
%              Number of equality atoms :   48 ( 210 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_subset_1 @ X14 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_subset_1 @ X14 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('40',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('49',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['26','35','44','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','54'])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v2_waybel_0 @ X11 @ ( k3_yellow_1 @ X9 ) )
      | ~ ( v13_waybel_0 @ X11 @ ( k3_yellow_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X9 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('63',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v2_waybel_0 @ X11 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) )
      | ~ ( v13_waybel_0 @ X11 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X10 @ X9 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('69',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_yellow_1 @ X6 ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_yellow_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X6 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('81',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('84',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('87',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','88'])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ~ ( r2_hidden @ X17 @ ( k10_yellow_6 @ X16 @ X15 ) )
      | ( r2_waybel_7 @ X16 @ ( k2_yellow19 @ X16 @ X15 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
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
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) ) ) )
      | ( X18
        = ( k2_yellow19 @ X19 @ ( k3_yellow19 @ X19 @ ( k2_struct_0 @ X19 ) @ X18 ) ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('104',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('105',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('106',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('107',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('108',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) ) ) )
      | ( X18
        = ( k2_yellow19 @ X19 @ ( k3_yellow19 @ X19 @ ( k2_struct_0 @ X19 ) @ X18 ) ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('111',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('112',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','120'])).

thf('122',plain,
    ( ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','121'])).

thf('123',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','122'])).

thf('124',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','124'])).

thf('126',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','128'])).

thf('130',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','130'])).

thf('132',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('137',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('138',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('140',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_yellow_1 @ X6 ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_yellow_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X6 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('141',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('142',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('143',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('144',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('147',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
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
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['138','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
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
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','152'])).

thf('154',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['135','153'])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('160',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['4','160'])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['3','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['167','168'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('170',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('171',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','173'])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['94'])).

thf('178',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('179',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('180',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('181',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('182',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['94'])).

thf('183',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('184',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('185',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('186',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('187',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('188',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v2_waybel_0 @ X11 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) )
      | ~ ( v13_waybel_0 @ X11 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X10 @ X9 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('191',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['186','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['185','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['184','196'])).

thf('198',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('202',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('203',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('204',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('205',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('206',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_subset_1 @ X14 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('207',plain,(
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
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('209',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('210',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['207','208','209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['204','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['203','212'])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['202','215'])).

thf('217',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['201','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('221',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('222',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('223',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('224',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('225',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('228',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['223','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['222','230'])).

thf('232',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['221','233'])).

thf('235',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['220','234'])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('239',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ~ ( r2_waybel_7 @ X16 @ ( k2_yellow19 @ X16 @ X15 ) @ X17 )
      | ( r2_hidden @ X17 @ ( k10_yellow_6 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['237','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['219','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['200','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['182','249'])).

thf('251',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('254',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','152'])).

thf('256',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','257'])).

thf('259',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('263',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['180','264'])).

thf('266',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['179','265'])).

thf('267',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('270',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','272'])).

thf('274',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','176','177','275'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOQ8sXfqNu
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 173 iterations in 0.078s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.35/0.54  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.54  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.35/0.54  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.35/0.54  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.35/0.54  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.35/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.35/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.54  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.35/0.54  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.35/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.35/0.54  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.35/0.54  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.35/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.35/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.35/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.54  thf(t18_yellow19, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.54             ( v1_subset_1 @
% 0.35/0.54               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.35/0.54             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.35/0.54             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.35/0.54             ( m1_subset_1 @
% 0.35/0.54               B @ 
% 0.35/0.54               ( k1_zfmisc_1 @
% 0.35/0.54                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.54               ( ( r2_hidden @
% 0.35/0.54                   C @ 
% 0.35/0.54                   ( k10_yellow_6 @
% 0.35/0.54                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.35/0.54                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.54            ( l1_pre_topc @ A ) ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.54                ( v1_subset_1 @
% 0.35/0.54                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.35/0.54                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.35/0.54                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.35/0.54                ( m1_subset_1 @
% 0.35/0.54                  B @ 
% 0.35/0.54                  ( k1_zfmisc_1 @
% 0.35/0.54                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.35/0.54              ( ![C:$i]:
% 0.35/0.54                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.54                  ( ( r2_hidden @
% 0.35/0.54                      C @ 
% 0.35/0.54                      ( k10_yellow_6 @
% 0.35/0.54                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.35/0.54                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54        | ~ (r2_hidden @ sk_C @ 
% 0.35/0.54             (k10_yellow_6 @ sk_A @ 
% 0.35/0.54              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.35/0.54       ~
% 0.35/0.54       ((r2_hidden @ sk_C @ 
% 0.35/0.54         (k10_yellow_6 @ sk_A @ 
% 0.35/0.54          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf(dt_l1_pre_topc, axiom,
% 0.35/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.54  thf('2', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('3', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf(d3_struct_0, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('5', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('6', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('7', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf(dt_k2_subset_1, axiom,
% 0.35/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.35/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.54  thf('9', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.54  thf('10', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('11', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d2_yellow_1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (((m1_subset_1 @ sk_B @ 
% 0.35/0.54         (k1_zfmisc_1 @ 
% 0.35/0.54          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['12', '15'])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (m1_subset_1 @ sk_B @ 
% 0.35/0.54           (k1_zfmisc_1 @ 
% 0.35/0.54            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '16'])).
% 0.35/0.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.35/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf(fc5_yellow19, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.35/0.54         ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.54         ( ~( v1_xboole_0 @ C ) ) & 
% 0.35/0.54         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.35/0.54         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.35/0.54         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.35/0.54         ( m1_subset_1 @
% 0.35/0.54           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.35/0.54       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.35/0.54         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.35/0.54         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.54          | (v1_xboole_0 @ X12)
% 0.35/0.54          | ~ (l1_struct_0 @ X13)
% 0.35/0.54          | (v2_struct_0 @ X13)
% 0.35/0.54          | (v1_xboole_0 @ X14)
% 0.35/0.54          | ~ (v1_subset_1 @ X14 @ (u1_struct_0 @ (k3_yellow_1 @ X12)))
% 0.35/0.54          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.35/0.54          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.35/0.54          | ~ (m1_subset_1 @ X14 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.35/0.54          | (v7_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.54          | (v1_xboole_0 @ X12)
% 0.35/0.54          | ~ (l1_struct_0 @ X13)
% 0.35/0.54          | (v2_struct_0 @ X13)
% 0.35/0.54          | (v1_xboole_0 @ X14)
% 0.35/0.54          | ~ (v1_subset_1 @ X14 @ 
% 0.35/0.54               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12))))
% 0.35/0.54          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.35/0.54          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.35/0.54          | ~ (m1_subset_1 @ X14 @ 
% 0.35/0.54               (k1_zfmisc_1 @ 
% 0.35/0.54                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.35/0.54          | (v7_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.35/0.54      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54          | ~ (v13_waybel_0 @ sk_B @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54          | ~ (v2_waybel_0 @ sk_B @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54          | ~ (v1_subset_1 @ sk_B @ 
% 0.35/0.54               (u1_struct_0 @ 
% 0.35/0.54                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['19', '25'])).
% 0.35/0.54  thf('27', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      ((v13_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (((v13_waybel_0 @ sk_B @ 
% 0.35/0.54         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['28', '31'])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (v13_waybel_0 @ sk_B @ 
% 0.35/0.54           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['27', '32'])).
% 0.35/0.54  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      ((v13_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.54  thf('36', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      ((v2_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      (((v2_waybel_0 @ sk_B @ 
% 0.35/0.54         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['37', '40'])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (v2_waybel_0 @ sk_B @ 
% 0.35/0.54           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['36', '41'])).
% 0.35/0.54  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      ((v2_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.35/0.54  thf('45', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      ((v1_subset_1 @ sk_B @ 
% 0.35/0.54        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      ((v1_subset_1 @ sk_B @ 
% 0.35/0.54        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['47', '48'])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      (((v1_subset_1 @ sk_B @ 
% 0.35/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['46', '49'])).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (v1_subset_1 @ sk_B @ 
% 0.35/0.54           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['45', '50'])).
% 0.35/0.54  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      ((v1_subset_1 @ sk_B @ 
% 0.35/0.54        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['26', '35', '44', '53'])).
% 0.35/0.54  thf('55', plain,
% 0.35/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['10', '54'])).
% 0.35/0.54  thf('56', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['7', '55'])).
% 0.35/0.54  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['56', '57'])).
% 0.35/0.54  thf('59', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('60', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('61', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.35/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf(fc4_yellow19, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.35/0.54         ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.54         ( ~( v1_xboole_0 @ C ) ) & 
% 0.35/0.54         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.35/0.54         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.35/0.54         ( m1_subset_1 @
% 0.35/0.54           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.35/0.54       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.35/0.54         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.35/0.54         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.35/0.54         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.35/0.54  thf('62', plain,
% 0.35/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.35/0.54          | (v1_xboole_0 @ X9)
% 0.35/0.54          | ~ (l1_struct_0 @ X10)
% 0.35/0.54          | (v2_struct_0 @ X10)
% 0.35/0.54          | (v1_xboole_0 @ X11)
% 0.35/0.54          | ~ (v2_waybel_0 @ X11 @ (k3_yellow_1 @ X9))
% 0.35/0.54          | ~ (v13_waybel_0 @ X11 @ (k3_yellow_1 @ X9))
% 0.35/0.54          | ~ (m1_subset_1 @ X11 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X9))))
% 0.35/0.54          | (v4_orders_2 @ (k3_yellow19 @ X10 @ X9 @ X11)))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.35/0.54  thf('63', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('64', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('65', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('66', plain,
% 0.35/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.35/0.54          | (v1_xboole_0 @ X9)
% 0.35/0.54          | ~ (l1_struct_0 @ X10)
% 0.35/0.54          | (v2_struct_0 @ X10)
% 0.35/0.54          | (v1_xboole_0 @ X11)
% 0.35/0.54          | ~ (v2_waybel_0 @ X11 @ (k3_lattice3 @ (k1_lattice3 @ X9)))
% 0.35/0.54          | ~ (v13_waybel_0 @ X11 @ (k3_lattice3 @ (k1_lattice3 @ X9)))
% 0.35/0.54          | ~ (m1_subset_1 @ X11 @ 
% 0.35/0.54               (k1_zfmisc_1 @ 
% 0.35/0.54                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X9)))))
% 0.35/0.54          | (v4_orders_2 @ (k3_yellow19 @ X10 @ X9 @ X11)))),
% 0.35/0.54      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.35/0.54  thf('67', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54          | ~ (v13_waybel_0 @ sk_B @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54          | ~ (v2_waybel_0 @ sk_B @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['61', '66'])).
% 0.35/0.54  thf('68', plain,
% 0.35/0.54      ((v13_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.54  thf('69', plain,
% 0.35/0.54      ((v2_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.35/0.54  thf('70', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.35/0.54  thf('71', plain,
% 0.35/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['60', '70'])).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['59', '71'])).
% 0.35/0.54  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('74', plain,
% 0.35/0.54      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['72', '73'])).
% 0.35/0.54  thf('75', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('76', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('77', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('78', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('79', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.35/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf(dt_k3_yellow19, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.35/0.54         ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.54         ( ~( v1_xboole_0 @ C ) ) & 
% 0.35/0.54         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.35/0.54         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.35/0.54         ( m1_subset_1 @
% 0.35/0.54           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.35/0.54       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.35/0.54         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.35/0.54         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.35/0.54  thf('80', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.35/0.54          | (v1_xboole_0 @ X6)
% 0.35/0.54          | ~ (l1_struct_0 @ X7)
% 0.35/0.54          | (v2_struct_0 @ X7)
% 0.35/0.54          | (v1_xboole_0 @ X8)
% 0.35/0.54          | ~ (v2_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.35/0.54          | ~ (v13_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.35/0.54          | ~ (m1_subset_1 @ X8 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X6))))
% 0.35/0.54          | (l1_waybel_0 @ (k3_yellow19 @ X7 @ X6 @ X8) @ X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.35/0.54  thf('81', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('82', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('83', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('84', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.35/0.54          | (v1_xboole_0 @ X6)
% 0.35/0.54          | ~ (l1_struct_0 @ X7)
% 0.35/0.54          | (v2_struct_0 @ X7)
% 0.35/0.54          | (v1_xboole_0 @ X8)
% 0.35/0.54          | ~ (v2_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.35/0.54          | ~ (v13_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.35/0.54          | ~ (m1_subset_1 @ X8 @ 
% 0.35/0.54               (k1_zfmisc_1 @ 
% 0.35/0.54                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X6)))))
% 0.35/0.54          | (l1_waybel_0 @ (k3_yellow19 @ X7 @ X6 @ X8) @ X7))),
% 0.35/0.54      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.35/0.54  thf('85', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.35/0.54          | ~ (v13_waybel_0 @ sk_B @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54          | ~ (v2_waybel_0 @ sk_B @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['79', '84'])).
% 0.35/0.54  thf('86', plain,
% 0.35/0.54      ((v13_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.54  thf('87', plain,
% 0.35/0.54      ((v2_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.35/0.54  thf('88', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.35/0.54  thf('89', plain,
% 0.35/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.54           sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['78', '88'])).
% 0.35/0.54  thf('90', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.54           sk_A)
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['77', '89'])).
% 0.35/0.54  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('92', plain,
% 0.35/0.54      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.54         sk_A)
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['90', '91'])).
% 0.35/0.54  thf('93', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('94', plain,
% 0.35/0.54      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54        | (r2_hidden @ sk_C @ 
% 0.35/0.54           (k10_yellow_6 @ sk_A @ 
% 0.35/0.54            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('95', plain,
% 0.35/0.54      (((r2_hidden @ sk_C @ 
% 0.35/0.54         (k10_yellow_6 @ sk_A @ 
% 0.35/0.54          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('split', [status(esa)], ['94'])).
% 0.35/0.54  thf(t13_yellow19, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.35/0.54             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.54               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) <=>
% 0.35/0.54                 ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.35/0.54  thf('96', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         ((v2_struct_0 @ X15)
% 0.35/0.54          | ~ (v4_orders_2 @ X15)
% 0.35/0.54          | ~ (v7_waybel_0 @ X15)
% 0.35/0.54          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.35/0.54          | ~ (r2_hidden @ X17 @ (k10_yellow_6 @ X16 @ X15))
% 0.35/0.54          | (r2_waybel_7 @ X16 @ (k2_yellow19 @ X16 @ X15) @ X17)
% 0.35/0.54          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.35/0.54          | ~ (l1_pre_topc @ X16)
% 0.35/0.54          | ~ (v2_pre_topc @ X16)
% 0.35/0.54          | (v2_struct_0 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.35/0.54  thf('97', plain,
% 0.35/0.54      ((((v2_struct_0 @ sk_A)
% 0.35/0.54         | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.35/0.54         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ 
% 0.35/0.54            (k2_yellow19 @ sk_A @ 
% 0.35/0.54             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.35/0.54            sk_C)
% 0.35/0.54         | ~ (l1_waybel_0 @ 
% 0.35/0.54              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.35/0.54  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('100', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('101', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('102', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf(t15_yellow19, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.54             ( v1_subset_1 @
% 0.35/0.54               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.35/0.54             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.35/0.54             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.35/0.54             ( m1_subset_1 @
% 0.35/0.54               B @ 
% 0.35/0.54               ( k1_zfmisc_1 @
% 0.35/0.54                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.35/0.54           ( ( B ) =
% 0.35/0.54             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.35/0.54  thf('103', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i]:
% 0.35/0.54         ((v1_xboole_0 @ X18)
% 0.35/0.54          | ~ (v1_subset_1 @ X18 @ 
% 0.35/0.54               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X19))))
% 0.35/0.54          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))
% 0.35/0.54          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ 
% 0.35/0.54               (k1_zfmisc_1 @ 
% 0.35/0.54                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))))
% 0.35/0.54          | ((X18)
% 0.35/0.54              = (k2_yellow19 @ X19 @ 
% 0.35/0.54                 (k3_yellow19 @ X19 @ (k2_struct_0 @ X19) @ X18)))
% 0.35/0.54          | ~ (l1_struct_0 @ X19)
% 0.35/0.54          | (v2_struct_0 @ X19))),
% 0.35/0.54      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.35/0.54  thf('104', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('105', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('106', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('107', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('108', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i]:
% 0.35/0.54         ((v1_xboole_0 @ X18)
% 0.35/0.54          | ~ (v1_subset_1 @ X18 @ 
% 0.35/0.54               (u1_struct_0 @ 
% 0.35/0.54                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19)))))
% 0.35/0.54          | ~ (v2_waybel_0 @ X18 @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))
% 0.35/0.54          | ~ (v13_waybel_0 @ X18 @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ 
% 0.35/0.54               (k1_zfmisc_1 @ 
% 0.35/0.54                (u1_struct_0 @ 
% 0.35/0.54                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))))
% 0.35/0.54          | ((X18)
% 0.35/0.54              = (k2_yellow19 @ X19 @ 
% 0.35/0.54                 (k3_yellow19 @ X19 @ (k2_struct_0 @ X19) @ X18)))
% 0.35/0.54          | ~ (l1_struct_0 @ X19)
% 0.35/0.54          | (v2_struct_0 @ X19))),
% 0.35/0.54      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.35/0.54  thf('109', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54        | ((sk_B)
% 0.35/0.54            = (k2_yellow19 @ sk_A @ 
% 0.35/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.35/0.54        | ~ (v13_waybel_0 @ sk_B @ 
% 0.35/0.54             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.35/0.54        | ~ (v2_waybel_0 @ sk_B @ 
% 0.35/0.54             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.35/0.54        | ~ (v1_subset_1 @ sk_B @ 
% 0.35/0.54             (u1_struct_0 @ 
% 0.35/0.54              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.35/0.54        | (v1_xboole_0 @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['102', '108'])).
% 0.35/0.54  thf('110', plain,
% 0.35/0.54      ((v13_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('111', plain,
% 0.35/0.54      ((v2_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.54  thf('112', plain,
% 0.35/0.54      ((v1_subset_1 @ sk_B @ 
% 0.35/0.54        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['47', '48'])).
% 0.35/0.54  thf('113', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54        | ((sk_B)
% 0.35/0.54            = (k2_yellow19 @ sk_A @ 
% 0.35/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.35/0.54        | (v1_xboole_0 @ sk_B))),
% 0.35/0.54      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.35/0.54  thf('114', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | ((sk_B)
% 0.35/0.54            = (k2_yellow19 @ sk_A @ 
% 0.35/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.35/0.54        | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['101', '113'])).
% 0.35/0.54  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('116', plain,
% 0.35/0.54      (((v1_xboole_0 @ sk_B)
% 0.35/0.54        | ((sk_B)
% 0.35/0.54            = (k2_yellow19 @ sk_A @ 
% 0.35/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.35/0.54        | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['114', '115'])).
% 0.35/0.54  thf('117', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('118', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | ((sk_B)
% 0.35/0.54            = (k2_yellow19 @ sk_A @ 
% 0.35/0.54               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.54      inference('clc', [status(thm)], ['116', '117'])).
% 0.35/0.54  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('120', plain,
% 0.35/0.54      (((sk_B)
% 0.35/0.54         = (k2_yellow19 @ sk_A @ 
% 0.35/0.54            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('clc', [status(thm)], ['118', '119'])).
% 0.35/0.54  thf('121', plain,
% 0.35/0.54      ((((v2_struct_0 @ sk_A)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | ~ (l1_waybel_0 @ 
% 0.35/0.54              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['97', '98', '99', '100', '120'])).
% 0.35/0.54  thf('122', plain,
% 0.35/0.54      (((~ (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.54            sk_A)
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v2_struct_0 @ sk_A)))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['93', '121'])).
% 0.35/0.54  thf('123', plain,
% 0.35/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['92', '122'])).
% 0.35/0.54  thf('124', plain,
% 0.35/0.54      (((~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['123'])).
% 0.35/0.54  thf('125', plain,
% 0.35/0.54      (((~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['76', '124'])).
% 0.35/0.54  thf('126', plain,
% 0.35/0.54      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['125'])).
% 0.35/0.54  thf('127', plain,
% 0.35/0.54      (((~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['75', '126'])).
% 0.35/0.54  thf('128', plain,
% 0.35/0.54      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['127'])).
% 0.35/0.54  thf('129', plain,
% 0.35/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['74', '128'])).
% 0.35/0.54  thf('130', plain,
% 0.35/0.54      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['129'])).
% 0.35/0.54  thf('131', plain,
% 0.35/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['58', '130'])).
% 0.35/0.54  thf('132', plain,
% 0.35/0.54      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['131'])).
% 0.35/0.54  thf('133', plain,
% 0.35/0.54      (((~ (l1_pre_topc @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '132'])).
% 0.35/0.54  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('135', plain,
% 0.35/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['133', '134'])).
% 0.35/0.54  thf('136', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('137', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('138', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('139', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.35/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('140', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.35/0.54          | (v1_xboole_0 @ X6)
% 0.35/0.54          | ~ (l1_struct_0 @ X7)
% 0.35/0.54          | (v2_struct_0 @ X7)
% 0.35/0.54          | (v1_xboole_0 @ X8)
% 0.35/0.54          | ~ (v2_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.35/0.54          | ~ (v13_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.35/0.54          | ~ (m1_subset_1 @ X8 @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X6))))
% 0.35/0.54          | ~ (v2_struct_0 @ (k3_yellow19 @ X7 @ X6 @ X8)))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.35/0.54  thf('141', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('142', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('143', plain,
% 0.35/0.54      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.35/0.54  thf('144', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.35/0.54          | (v1_xboole_0 @ X6)
% 0.35/0.54          | ~ (l1_struct_0 @ X7)
% 0.35/0.54          | (v2_struct_0 @ X7)
% 0.35/0.54          | (v1_xboole_0 @ X8)
% 0.35/0.54          | ~ (v2_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.35/0.54          | ~ (v13_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.35/0.54          | ~ (m1_subset_1 @ X8 @ 
% 0.35/0.54               (k1_zfmisc_1 @ 
% 0.35/0.54                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X6)))))
% 0.35/0.54          | ~ (v2_struct_0 @ (k3_yellow19 @ X7 @ X6 @ X8)))),
% 0.35/0.54      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.35/0.54  thf('145', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54          | ~ (v13_waybel_0 @ sk_B @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.35/0.54          | ~ (v2_waybel_0 @ sk_B @ 
% 0.35/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['139', '144'])).
% 0.35/0.54  thf('146', plain,
% 0.35/0.54      ((v13_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('147', plain,
% 0.35/0.54      ((v2_waybel_0 @ sk_B @ 
% 0.35/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.35/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.54  thf('148', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.35/0.54  thf('149', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['138', '148'])).
% 0.35/0.54  thf('150', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ sk_A)
% 0.35/0.54          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['137', '149'])).
% 0.35/0.54  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('152', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.54          | (v1_xboole_0 @ sk_B)
% 0.35/0.54          | (v2_struct_0 @ X0)
% 0.35/0.54          | ~ (l1_struct_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.35/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.35/0.54      inference('demod', [status(thm)], ['150', '151'])).
% 0.35/0.54  thf('153', plain,
% 0.35/0.54      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ sk_B)
% 0.35/0.54        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['136', '152'])).
% 0.35/0.54  thf('154', plain,
% 0.35/0.54      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['135', '153'])).
% 0.35/0.54  thf('155', plain,
% 0.35/0.54      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['154'])).
% 0.35/0.54  thf('156', plain,
% 0.35/0.54      (((~ (l1_pre_topc @ sk_A)
% 0.35/0.54         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['5', '155'])).
% 0.35/0.54  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('158', plain,
% 0.35/0.54      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.35/0.54         <= (((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['156', '157'])).
% 0.35/0.54  thf('159', plain,
% 0.35/0.54      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('160', plain,
% 0.35/0.54      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['158', '159'])).
% 0.35/0.54  thf('161', plain,
% 0.35/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['4', '160'])).
% 0.35/0.54  thf('162', plain,
% 0.35/0.54      ((((v2_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('simplify', [status(thm)], ['161'])).
% 0.35/0.54  thf('163', plain,
% 0.35/0.54      (((~ (l1_pre_topc @ sk_A)
% 0.35/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['3', '162'])).
% 0.35/0.54  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('165', plain,
% 0.35/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54         | (v1_xboole_0 @ sk_B)
% 0.35/0.54         | (v2_struct_0 @ sk_A)))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['163', '164'])).
% 0.35/0.54  thf('166', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('167', plain,
% 0.35/0.54      ((((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('clc', [status(thm)], ['165', '166'])).
% 0.35/0.54  thf('168', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('169', plain,
% 0.35/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('clc', [status(thm)], ['167', '168'])).
% 0.35/0.54  thf(fc2_struct_0, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.54  thf('170', plain,
% 0.35/0.54      (![X4 : $i]:
% 0.35/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.35/0.54          | ~ (l1_struct_0 @ X4)
% 0.35/0.54          | (v2_struct_0 @ X4))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.54  thf('171', plain,
% 0.35/0.54      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['169', '170'])).
% 0.35/0.54  thf('172', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('173', plain,
% 0.35/0.54      ((~ (l1_struct_0 @ sk_A))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('clc', [status(thm)], ['171', '172'])).
% 0.35/0.54  thf('174', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A))
% 0.35/0.54         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.35/0.54             ((r2_hidden @ sk_C @ 
% 0.35/0.54               (k10_yellow_6 @ sk_A @ 
% 0.35/0.54                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '173'])).
% 0.35/0.54  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('176', plain,
% 0.35/0.54      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.35/0.54       ~
% 0.35/0.54       ((r2_hidden @ sk_C @ 
% 0.35/0.54         (k10_yellow_6 @ sk_A @ 
% 0.35/0.54          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.54      inference('demod', [status(thm)], ['174', '175'])).
% 0.35/0.54  thf('177', plain,
% 0.35/0.54      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.35/0.54       ((r2_hidden @ sk_C @ 
% 0.35/0.54         (k10_yellow_6 @ sk_A @ 
% 0.35/0.54          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.54      inference('split', [status(esa)], ['94'])).
% 0.35/0.54  thf('178', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('179', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('180', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('181', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('182', plain,
% 0.35/0.54      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.35/0.54         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.35/0.54      inference('split', [status(esa)], ['94'])).
% 0.35/0.54  thf('183', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('184', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('185', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.54  thf('186', plain,
% 0.35/0.54      (![X2 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('187', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ 
% 0.35/0.54        (k1_zfmisc_1 @ 
% 0.35/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.54  thf('188', plain,
% 0.38/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.54          | (v1_xboole_0 @ X9)
% 0.38/0.54          | ~ (l1_struct_0 @ X10)
% 0.38/0.54          | (v2_struct_0 @ X10)
% 0.38/0.54          | (v1_xboole_0 @ X11)
% 0.38/0.54          | ~ (v2_waybel_0 @ X11 @ (k3_lattice3 @ (k1_lattice3 @ X9)))
% 0.38/0.54          | ~ (v13_waybel_0 @ X11 @ (k3_lattice3 @ (k1_lattice3 @ X9)))
% 0.38/0.54          | ~ (m1_subset_1 @ X11 @ 
% 0.38/0.54               (k1_zfmisc_1 @ 
% 0.38/0.54                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X9)))))
% 0.38/0.54          | (v4_orders_2 @ (k3_yellow19 @ X10 @ X9 @ X11)))),
% 0.38/0.54      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.38/0.54  thf('189', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.54          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['187', '188'])).
% 0.38/0.54  thf('190', plain,
% 0.38/0.54      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.54  thf('191', plain,
% 0.38/0.54      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.54  thf('192', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('demod', [status(thm)], ['189', '190', '191'])).
% 0.38/0.54  thf('193', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['186', '192'])).
% 0.38/0.54  thf('194', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ sk_A)
% 0.38/0.54          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['185', '193'])).
% 0.38/0.54  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('196', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('demod', [status(thm)], ['194', '195'])).
% 0.38/0.54  thf('197', plain,
% 0.38/0.54      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.54        | (v2_struct_0 @ sk_A)
% 0.38/0.54        | (v1_xboole_0 @ sk_B)
% 0.38/0.54        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['184', '196'])).
% 0.38/0.54  thf('198', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.54        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54        | (v1_xboole_0 @ sk_B)
% 0.38/0.54        | (v2_struct_0 @ sk_A)
% 0.38/0.54        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['183', '197'])).
% 0.38/0.54  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('200', plain,
% 0.38/0.54      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54        | (v1_xboole_0 @ sk_B)
% 0.38/0.54        | (v2_struct_0 @ sk_A)
% 0.38/0.54        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.54      inference('demod', [status(thm)], ['198', '199'])).
% 0.38/0.54  thf('201', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.54  thf('202', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.38/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.54  thf('203', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.54  thf('204', plain,
% 0.38/0.54      (![X2 : $i]:
% 0.38/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.38/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.54  thf('205', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_B @ 
% 0.38/0.54        (k1_zfmisc_1 @ 
% 0.38/0.54         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.54  thf('206', plain,
% 0.38/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.54          | (v1_xboole_0 @ X12)
% 0.38/0.54          | ~ (l1_struct_0 @ X13)
% 0.38/0.54          | (v2_struct_0 @ X13)
% 0.38/0.54          | (v1_xboole_0 @ X14)
% 0.38/0.54          | ~ (v1_subset_1 @ X14 @ 
% 0.38/0.54               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12))))
% 0.38/0.54          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.38/0.54          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.38/0.54          | ~ (m1_subset_1 @ X14 @ 
% 0.38/0.54               (k1_zfmisc_1 @ 
% 0.38/0.54                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.38/0.54          | (v7_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.38/0.54      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.38/0.54  thf('207', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.54          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.54               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.54          | ~ (v1_subset_1 @ sk_B @ 
% 0.38/0.54               (u1_struct_0 @ 
% 0.38/0.54                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['205', '206'])).
% 0.38/0.54  thf('208', plain,
% 0.38/0.54      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.54  thf('209', plain,
% 0.38/0.54      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.54        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.54  thf('210', plain,
% 0.38/0.54      ((v1_subset_1 @ sk_B @ 
% 0.38/0.54        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.54      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.54  thf('211', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('demod', [status(thm)], ['207', '208', '209', '210'])).
% 0.38/0.54  thf('212', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['204', '211'])).
% 0.38/0.54  thf('213', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ sk_A)
% 0.38/0.54          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['203', '212'])).
% 0.38/0.54  thf('214', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('215', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54          | (v1_xboole_0 @ sk_B)
% 0.38/0.54          | (v2_struct_0 @ X0)
% 0.38/0.54          | ~ (l1_struct_0 @ X0)
% 0.38/0.54          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.54      inference('demod', [status(thm)], ['213', '214'])).
% 0.38/0.54  thf('216', plain,
% 0.38/0.54      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.54        | (v2_struct_0 @ sk_A)
% 0.38/0.54        | (v1_xboole_0 @ sk_B)
% 0.38/0.54        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['202', '215'])).
% 0.38/0.54  thf('217', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.54        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54        | (v1_xboole_0 @ sk_B)
% 0.38/0.54        | (v2_struct_0 @ sk_A)
% 0.38/0.54        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['201', '216'])).
% 0.38/0.54  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('219', plain,
% 0.38/0.54      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.54        | (v1_xboole_0 @ sk_B)
% 0.38/0.54        | (v2_struct_0 @ sk_A)
% 0.38/0.54        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.54      inference('demod', [status(thm)], ['217', '218'])).
% 0.38/0.54  thf('220', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.54  thf('221', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.38/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.54  thf('222', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.54  thf('223', plain,
% 0.38/0.54      (![X2 : $i]:
% 0.38/0.54         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.55  thf('224', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.55  thf('225', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.55          | (v1_xboole_0 @ X6)
% 0.38/0.55          | ~ (l1_struct_0 @ X7)
% 0.38/0.55          | (v2_struct_0 @ X7)
% 0.38/0.55          | (v1_xboole_0 @ X8)
% 0.38/0.55          | ~ (v2_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.38/0.55          | ~ (v13_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.38/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X6)))))
% 0.38/0.55          | (l1_waybel_0 @ (k3_yellow19 @ X7 @ X6 @ X8) @ X7))),
% 0.38/0.55      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.38/0.55  thf('226', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.55          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.55          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['224', '225'])).
% 0.38/0.55  thf('227', plain,
% 0.38/0.55      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('228', plain,
% 0.38/0.55      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.55  thf('229', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.55      inference('demod', [status(thm)], ['226', '227', '228'])).
% 0.38/0.55  thf('230', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.55             X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['223', '229'])).
% 0.38/0.55  thf('231', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | (l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['222', '230'])).
% 0.38/0.55  thf('232', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('233', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.55      inference('demod', [status(thm)], ['231', '232'])).
% 0.38/0.55  thf('234', plain,
% 0.38/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ sk_B)
% 0.38/0.55        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.55           sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['221', '233'])).
% 0.38/0.55  thf('235', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.55           sk_A)
% 0.38/0.55        | (v1_xboole_0 @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['220', '234'])).
% 0.38/0.55  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('237', plain,
% 0.38/0.55      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.55         sk_A)
% 0.38/0.55        | (v1_xboole_0 @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['235', '236'])).
% 0.38/0.55  thf('238', plain,
% 0.38/0.55      (((sk_B)
% 0.38/0.55         = (k2_yellow19 @ sk_A @ 
% 0.38/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.55      inference('clc', [status(thm)], ['118', '119'])).
% 0.38/0.55  thf('239', plain,
% 0.38/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X15)
% 0.38/0.55          | ~ (v4_orders_2 @ X15)
% 0.38/0.55          | ~ (v7_waybel_0 @ X15)
% 0.38/0.55          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.38/0.55          | ~ (r2_waybel_7 @ X16 @ (k2_yellow19 @ X16 @ X15) @ X17)
% 0.38/0.55          | (r2_hidden @ X17 @ (k10_yellow_6 @ X16 @ X15))
% 0.38/0.55          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.38/0.55          | ~ (l1_pre_topc @ X16)
% 0.38/0.55          | ~ (v2_pre_topc @ X16)
% 0.38/0.55          | (v2_struct_0 @ X16))),
% 0.38/0.55      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.38/0.55  thf('240', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55          | (r2_hidden @ X0 @ 
% 0.38/0.55             (k10_yellow_6 @ sk_A @ 
% 0.38/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55          | ~ (l1_waybel_0 @ 
% 0.38/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['238', '239'])).
% 0.38/0.55  thf('241', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('243', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55          | (r2_hidden @ X0 @ 
% 0.38/0.55             (k10_yellow_6 @ sk_A @ 
% 0.38/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55          | ~ (l1_waybel_0 @ 
% 0.38/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['240', '241', '242'])).
% 0.38/0.55  thf('244', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (r2_hidden @ X0 @ 
% 0.38/0.55             (k10_yellow_6 @ sk_A @ 
% 0.38/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['237', '243'])).
% 0.38/0.55  thf('245', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55          | (r2_hidden @ X0 @ 
% 0.38/0.55             (k10_yellow_6 @ sk_A @ 
% 0.38/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['244'])).
% 0.38/0.55  thf('246', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (r2_hidden @ X0 @ 
% 0.38/0.55             (k10_yellow_6 @ sk_A @ 
% 0.38/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['219', '245'])).
% 0.38/0.55  thf('247', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55          | (r2_hidden @ X0 @ 
% 0.38/0.55             (k10_yellow_6 @ sk_A @ 
% 0.38/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['246'])).
% 0.38/0.55  thf('248', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (r2_hidden @ X0 @ 
% 0.38/0.55             (k10_yellow_6 @ sk_A @ 
% 0.38/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['200', '247'])).
% 0.38/0.55  thf('249', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55          | (r2_hidden @ X0 @ 
% 0.38/0.55             (k10_yellow_6 @ sk_A @ 
% 0.38/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55          | (v1_xboole_0 @ sk_B)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['248'])).
% 0.38/0.55  thf('250', plain,
% 0.38/0.55      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55         | (v2_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ sk_B)
% 0.38/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55         | (r2_hidden @ sk_C @ 
% 0.38/0.55            (k10_yellow_6 @ sk_A @ 
% 0.38/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.55         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.38/0.55         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['182', '249'])).
% 0.38/0.55  thf('251', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('252', plain,
% 0.38/0.55      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55         | (v2_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ sk_B)
% 0.38/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55         | (r2_hidden @ sk_C @ 
% 0.38/0.55            (k10_yellow_6 @ sk_A @ 
% 0.38/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.38/0.55         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('demod', [status(thm)], ['250', '251'])).
% 0.38/0.55  thf('253', plain,
% 0.38/0.55      ((~ (r2_hidden @ sk_C @ 
% 0.38/0.55           (k10_yellow_6 @ sk_A @ 
% 0.38/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('254', plain,
% 0.38/0.55      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.55         | (v1_xboole_0 @ sk_B)
% 0.38/0.55         | (v2_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['252', '253'])).
% 0.38/0.55  thf('255', plain,
% 0.38/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ sk_B)
% 0.38/0.55        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['136', '152'])).
% 0.38/0.55  thf('256', plain,
% 0.38/0.55      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55         | (v2_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ sk_B)
% 0.38/0.55         | (v1_xboole_0 @ sk_B)
% 0.38/0.55         | (v2_struct_0 @ sk_A)
% 0.38/0.55         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['254', '255'])).
% 0.38/0.55  thf('257', plain,
% 0.38/0.55      (((~ (l1_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ sk_B)
% 0.38/0.55         | (v2_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['256'])).
% 0.38/0.55  thf('258', plain,
% 0.38/0.55      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55         | (v2_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ sk_B)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['181', '257'])).
% 0.38/0.55  thf('259', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('260', plain,
% 0.38/0.55      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.55         | (v2_struct_0 @ sk_A)
% 0.38/0.55         | (v1_xboole_0 @ sk_B)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('demod', [status(thm)], ['258', '259'])).
% 0.38/0.55  thf('261', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('262', plain,
% 0.38/0.55      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('clc', [status(thm)], ['260', '261'])).
% 0.38/0.55  thf('263', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('264', plain,
% 0.38/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('clc', [status(thm)], ['262', '263'])).
% 0.38/0.55  thf('265', plain,
% 0.38/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['180', '264'])).
% 0.38/0.55  thf('266', plain,
% 0.38/0.55      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['179', '265'])).
% 0.38/0.55  thf('267', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('268', plain,
% 0.38/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('demod', [status(thm)], ['266', '267'])).
% 0.38/0.55  thf('269', plain,
% 0.38/0.55      (![X4 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.38/0.55          | ~ (l1_struct_0 @ X4)
% 0.38/0.55          | (v2_struct_0 @ X4))),
% 0.38/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.55  thf('270', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['268', '269'])).
% 0.38/0.55  thf('271', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('272', plain,
% 0.38/0.55      ((~ (l1_struct_0 @ sk_A))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('clc', [status(thm)], ['270', '271'])).
% 0.38/0.55  thf('273', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ sk_C @ 
% 0.38/0.55               (k10_yellow_6 @ sk_A @ 
% 0.38/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['178', '272'])).
% 0.38/0.55  thf('274', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('275', plain,
% 0.38/0.55      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.55       ((r2_hidden @ sk_C @ 
% 0.38/0.55         (k10_yellow_6 @ sk_A @ 
% 0.38/0.55          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.55      inference('demod', [status(thm)], ['273', '274'])).
% 0.38/0.55  thf('276', plain, ($false),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['1', '176', '177', '275'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
